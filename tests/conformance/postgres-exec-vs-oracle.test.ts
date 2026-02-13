import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql } from "../../adapters/postgres/src/lower/query-to-sql"
import { lowerBoolQueryConstraintToSql } from "../../adapters/postgres/src/lower/constraint-to-sql"
import { installPostgresSchemaV0, openPgMemory, runLoweredQueryPlan, runPlanAll, upsertSlaStatus, upsertSnapshot } from "../harness/pg-memory"

function canonRows (rows: any[]): any[] {
  const norm = rows.map((r) => stableNormalize(r))
  norm.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)))
  return norm
}

function stableNormalize (v: any): any {
  if (v === null || typeof v !== "object") return v
  if (Array.isArray(v)) return v.map(stableNormalize)
  const out: any = {}
  for (const k of Object.keys(v).sort()) out[k] = stableNormalize(v[k])
  return out
}

describe("conformance: postgres execution vs oracle", () => {
  it("exec lowered view query equals oracle rows (project/filter/order/limit)", async () => {
    const pg = await openPgMemory()
    try {
      await installPostgresSchemaV0(pg.pool)

      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1, severity_i: 2, created_at: 10 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "triage", attrs: {}, updated_ts: 1, severity_i: 3, created_at: 5 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "new", attrs: {}, updated_ts: 1, severity_i: 1, created_at: 1 })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          { filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } },
          {
            project: {
              fields: [
                { name: "id", expr: { var: { row: { field: "entity_id" } } } },
                { name: "sev", expr: { var: { row: { field: "severity_i" } } } },
                { name: "ts", expr: { var: { row: { field: "created_at" } } } },
              ],
            },
          },
          { order_by: [{ expr: { var: { row: { field: "sev" } } }, dir: "desc" }, { expr: { var: { row: { field: "ts" } } }, dir: "asc" }] },
          { limit: 10 },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = await runLoweredQueryPlan(pg.pool, { tenant_id: "t", query: q, plan })

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [
          { entity_id: "a", state: "new", severity_i: 2, created_at: 10 },
          { entity_id: "b", state: "triage", severity_i: 3, created_at: 5 },
          { entity_id: "c", state: "new", severity_i: 1, created_at: 1 },
        ],
        sla_status: () => [],
        baseEnv: {
          now: 1,
          actor: "u",
          state: "",
          input: {},
          attrs: {},
          arg: {},
          intrinsics: {
            has_role: () => false,
            role_of: () => "agent",
            auth_ok: () => true,
            constraint: () => true,
            len: () => 0,
            str: (v: any) => (v === null ? null : String(v)),
            int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
            float: (v: any) => (typeof v === "number" ? v : null),
          },
        },
      }

      const oracle = interpretQuery(q, ctx)
      const sqlProjected = sqlRows.map((r: any) => ({ id: r.id, sev: r.sev, ts: r.ts }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      await pg.close()
    }
  })

  it("exec lowered bool_query constraint equals oracle truth", async () => {
    const pg = await openPgMemory()
    try {
      await installPostgresSchemaV0(pg.pool)

      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1 })

      const constraint: any = {
        kind: "bool_query",
        on_type: "Ticket",
        args: { limit: { type: "int" } },
        query: {
          source: { snap: { type: "Ticket" } },
          pipeline: [{ filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } }],
        },
        assert: { le: [{ var: { rows_count: true } }, { var: { arg: { name: "limit" } } }] },
      }

      const plan = lowerBoolQueryConstraintToSql({ constraint, version: 0, tenant_id: "t", args: { limit: 2 } })
      const row = (await runPlanAll(pg.pool, plan.sql, plan.binds))[0]
      assert.ok(row)
      const okPg = row.ok === 1 || row.ok === true

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [
          { entity_id: "a", state: "new" },
          { entity_id: "b", state: "new" },
          { entity_id: "c", state: "triage" },
        ],
        sla_status: () => [],
        baseEnv: {
          now: 1,
          actor: "u",
          state: "",
          input: {},
          attrs: {},
          arg: {},
          intrinsics: {
            has_role: () => false,
            role_of: () => "agent",
            auth_ok: () => true,
            constraint: () => true,
            len: () => 0,
            str: (v: any) => (v === null ? null : String(v)),
            int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
            float: (v: any) => (typeof v === "number" ? v : null),
          },
        },
      }

      const qOut = interpretQuery(constraint.query, ctx)
      const okOracle = qOut.rows_count <= 2
      assert.equal(okPg, okOracle)
    } finally {
      await pg.close()
    }
  })

  it("exec lowered join query equals oracle rows", async () => {
    const pg = await openPgMemory()
    try {
      await installPostgresSchemaV0(pg.pool)

      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1 })
      await upsertSlaStatus(pg.pool, { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "a", breached: false, updated_ts: 1 })
      await upsertSlaStatus(pg.pool, { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "b", breached: true, updated_ts: 1 })

      const q: any = {
        source: {
          join: {
            left: { snap: { type: "Ticket" } },
            right: { sla_status: { name: "response", on_type: "Ticket" } },
            on: { left_field: "entity_id", right_field: "entity_id" },
          },
        },
        pipeline: [
          { filter: { eq: [{ var: { row: { field: "breached" } } }, { lit: { bool: false } }] } },
          { project: { fields: [{ name: "id", expr: { var: { row: { field: "entity_id" } } } }] } },
          { order_by: [{ expr: { var: { row: { field: "id" } } }, dir: "asc" }] },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = await runLoweredQueryPlan(pg.pool, { tenant_id: "t", query: q, plan })

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [{ entity_id: "a", state: "new" }, { entity_id: "b", state: "new" }],
        sla_status: () => [{ entity_id: "a", breached: false }, { entity_id: "b", breached: true }],
        baseEnv: {
          now: 1,
          actor: "u",
          state: "",
          input: {},
          attrs: {},
          arg: {},
          intrinsics: {
            has_role: () => false,
            role_of: () => "agent",
            auth_ok: () => true,
            constraint: () => true,
            len: () => 0,
            str: (v: any) => (v === null ? null : String(v)),
            int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
            float: (v: any) => (typeof v === "number" ? v : null),
          },
        },
      }

      const oracle = interpretQuery(q, ctx)
      const sqlProjected = sqlRows.map((r: any) => ({ id: r.id }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      await pg.close()
    }
  })

  it("exec lowered grouped query with offset equals oracle rows", async () => {
    const pg = await openPgMemory()
    try {
      await installPostgresSchemaV0(pg.pool)

      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "d", state: "triage", attrs: {}, updated_ts: 1 })
      await upsertSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "e", state: "triage", attrs: {}, updated_ts: 1 })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          {
            group_by: {
              keys: [{ name: "state", expr: { var: { row: { field: "state" } } } }],
              aggs: [{ name: "count", expr: { count: { var: { row: { field: "entity_id" } } } } }],
            },
          },
          { order_by: [{ expr: { var: { row: { field: "state" } } }, dir: "asc" }] },
          { offset: 1 },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = await runLoweredQueryPlan(pg.pool, { tenant_id: "t", query: q, plan })

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [
          { entity_id: "a", state: "new" },
          { entity_id: "b", state: "new" },
          { entity_id: "c", state: "triage" },
          { entity_id: "d", state: "triage" },
          { entity_id: "e", state: "triage" },
        ],
        sla_status: () => [],
        baseEnv: {
          now: 1,
          actor: "u",
          state: "",
          input: {},
          attrs: {},
          arg: {},
          intrinsics: {
            has_role: () => false,
            role_of: () => "agent",
            auth_ok: () => true,
            constraint: () => true,
            len: () => 0,
            str: (v: any) => (v === null ? null : String(v)),
            int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
            float: (v: any) => (typeof v === "number" ? v : null),
          },
        },
      }

      const oracle = interpretQuery(q, ctx)
      assert.deepEqual(canonRows(sqlRows), canonRows(oracle.rows))
    } finally {
      await pg.close()
    }
  })
})
