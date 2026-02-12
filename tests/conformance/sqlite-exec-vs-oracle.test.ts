// /tests/conformance/sqlite-exec-vs-oracle.test.ts

import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { lowerBoolQueryConstraintToSql } from "../../adapters/sqlite/src/lower/constraint-to-sql"

import { installSqliteSchemaV0, openSqliteMemory, runLoweredQueryPlan, runPlanAll, upsertSlaStatus, upsertSnapshot } from "../harness/sqlite-memory"

function canonRows (rows: any[]): any[] {
  // stable ordering + JSON normalization for comparison
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

describe("conformance: sqlite execution vs oracle", () => {
  it("exec lowered view query equals oracle rows (project/filter/order/limit)", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1, severity_i: 2, created_at: 10 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "triage", attrs: {}, updated_ts: 1, severity_i: 3, created_at: 5 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "new", attrs: {}, updated_ts: 1, severity_i: 1, created_at: 1 })

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
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

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

      // SQL returns columns plus extras if we used '*' in lowering; enforce only projected columns
      const sqlProjected = sqlRows.map((r: any) => ({ id: r.id, sev: r.sev, ts: r.ts }))

      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })

  it("exec lowered bool_query constraint ok equals oracle truth (rows_count <= limit)", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1 })

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

      // SQL
      const plan = lowerBoolQueryConstraintToSql({ constraint, version: 0, tenant_id: "t", args: { limit: 2 } })
      const row = runPlanAll(db, plan.sql, plan.binds)[0]
      assert.ok(row)
      const okSql = row.ok === 1 || row.ok === true

      // Oracle
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

      assert.equal(okSql, okOracle)
    } finally {
      db.close()
    }
  })

  it("exec lowered bool_query arithmetic assert equals oracle truth", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1 })

      const constraint: any = {
        kind: "bool_query",
        on_type: "Ticket",
        args: { delta: { type: "int" } },
        query: {
          source: { snap: { type: "Ticket" } },
          pipeline: [{ filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } }],
        },
        assert: { eq: [{ add: [{ var: { rows_count: true } }, { var: { arg: { name: "delta" } } }] }, { lit: { int: 3 } }] },
      }

      const plan = lowerBoolQueryConstraintToSql({ constraint, version: 0, tenant_id: "t", args: { delta: 1 } })
      const row = runPlanAll(db, plan.sql, plan.binds)[0]
      assert.ok(row)
      const okSql = row.ok === 1 || row.ok === true

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
      const okOracle = (qOut.rows_count + 1) === 3

      assert.equal(okSql, okOracle)
    } finally {
      db.close()
    }
  })

  it("exec lowered query equals oracle rows for group_by + aggregations", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1, severity_i: 2 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1, severity_i: 3 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1, severity_i: 1 })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          {
            group_by: {
              keys: [{ name: "state", expr: { var: { row: { field: "state" } } } }],
              aggs: {
                rows_count: { count: {} },
                sev_sum: { sum: { expr: { var: { row: { field: "severity_i" } } } } },
              },
            },
          },
          { order_by: [{ expr: { var: { row: { field: "state" } } }, dir: "asc" }] },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [
          { entity_id: "a", state: "new", severity_i: 2 },
          { entity_id: "b", state: "new", severity_i: 3 },
          { entity_id: "c", state: "triage", severity_i: 1 },
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
      const sqlProjected = sqlRows.map((r: any) => ({ state: r.state, rows_count: r.rows_count, sev_sum: r.sev_sum }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })

  it("exec lowered query equals oracle rows for join source", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1 })

      upsertSlaStatus(db, { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "a", breached: 0, updated_ts: 1 })
      upsertSlaStatus(db, { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "b", breached: 1, updated_ts: 1 })

      const q: any = {
        source: {
          join: {
            left: { snap: { type: "Ticket" } },
            right: { sla_status: { name: "response", on_type: "Ticket" } },
            on: { left_field: "entity_id", right_field: "entity_id" },
          },
        },
        pipeline: [
          { filter: { eq: [{ var: { row: { field: "breached" } } }, { lit: { int: 0 } }] } },
          {
            project: {
              fields: [
                { name: "id", expr: { var: { row: { field: "entity_id" } } } },
                { name: "state", expr: { var: { row: { field: "state" } } } },
              ],
            },
          },
          { order_by: [{ expr: { var: { row: { field: "id" } } }, dir: "asc" }] },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [
          { entity_id: "a", state: "new" },
          { entity_id: "b", state: "new" },
          { entity_id: "c", state: "triage" },
        ],
        sla_status: () => [
          { entity_id: "a", breached: 0 },
          { entity_id: "b", breached: 1 },
        ],
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
      const sqlProjected = sqlRows.map((r: any) => ({ id: r.id, state: r.state }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })

  it("exec lowered query equals oracle rows for direct sla_status source", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSlaStatus(db, { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "a", breached: 0, updated_ts: 1 })
      upsertSlaStatus(db, { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "b", breached: 1, updated_ts: 1 })
      upsertSlaStatus(db, { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "c", breached: 1, updated_ts: 1 })

      const q: any = {
        source: { sla_status: { name: "response", on_type: "Ticket" } },
        pipeline: [
          { filter: { eq: [{ var: { row: { field: "breached" } } }, { lit: { int: 1 } }] } },
          {
            project: {
              fields: [
                { name: "id", expr: { var: { row: { field: "entity_id" } } } },
                { name: "breached", expr: { var: { row: { field: "breached" } } } },
              ],
            },
          },
          { order_by: [{ expr: { var: { row: { field: "id" } } }, dir: "asc" }] },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [],
        sla_status: () => [
          { entity_id: "a", breached: 0 },
          { entity_id: "b", breached: 1 },
          { entity_id: "c", breached: 1 },
        ],
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
      const sqlProjected = sqlRows.map((r: any) => ({ id: r.id, breached: r.breached }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })

  it("exec lowered query equals oracle rows for expr operator coverage", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1 })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          {
            project: {
              fields: [
                { name: "co", expr: { coalesce: [{ lit: { null: true } }, { lit: { string: "fallback" } }] } },
                {
                  name: "iff",
                  expr: {
                    if: {
                      cond: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] },
                      then: { lit: { int: 1 } },
                      else: { lit: { int: 0 } },
                    },
                  },
                },
                {
                  name: "isin",
                  expr: {
                    in: {
                      needle: { var: { row: { field: "state" } } },
                      haystack: { arr: { items: [{ lit: { string: "new" } }, { lit: { string: "done" } }] } },
                    },
                  },
                },
                {
                  name: "mapped",
                  expr: {
                    map_enum: {
                      expr: { var: { row: { field: "state" } } },
                      mapping: { new: 10, done: 20 },
                    },
                  },
                },
              ],
            },
          },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [{ entity_id: "a", state: "new" }],
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
      const sqlProjected = sqlRows.map((r: any) => ({ co: r.co, iff: r.iff, isin: r.isin, mapped: r.mapped }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })

  it("exec lowered query equals oracle rows for broad expr operator matrix", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "a",
        state: "new",
        attrs: { foo: { bar: 7 }, s: "12", n: 3 },
        updated_ts: 1,
        severity_i: 2,
        created_at: 5,
      })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          {
            project: {
              fields: [
                { name: "not1", expr: { not: { lit: { bool: false } } } },
                { name: "and1", expr: { and: [{ lit: { bool: true } }, { lit: { bool: true } }] } },
                { name: "or1", expr: { or: [{ lit: { bool: false } }, { lit: { bool: true } }] } },
                { name: "eq1", expr: { eq: [{ lit: { int: 1 } }, { lit: { int: 1 } }] } },
                { name: "ne1", expr: { ne: [{ lit: { int: 1 } }, { lit: { int: 2 } }] } },
                { name: "lt1", expr: { lt: [{ lit: { int: 1 } }, { lit: { int: 2 } }] } },
                { name: "le1", expr: { le: [{ lit: { int: 2 } }, { lit: { int: 2 } }] } },
                { name: "gt1", expr: { gt: [{ lit: { int: 3 } }, { lit: { int: 2 } }] } },
                { name: "ge1", expr: { ge: [{ lit: { int: 3 } }, { lit: { int: 3 } }] } },
                { name: "add1", expr: { add: [{ lit: { int: 2 } }, { lit: { int: 3 } }] } },
                { name: "sub1", expr: { sub: [{ lit: { int: 5 } }, { lit: { int: 3 } }] } },
                { name: "mul1", expr: { mul: [{ lit: { int: 2 } }, { lit: { int: 4 } }] } },
                { name: "div1", expr: { div: [{ lit: { int: 8 } }, { lit: { int: 2 } }] } },
                { name: "if1", expr: { if: { cond: { lit: { bool: true } }, then: { lit: { int: 1 } }, else: { lit: { int: 0 } } } } },
                { name: "coal1", expr: { coalesce: [{ lit: { null: true } }, { lit: { string: "x" } }] } },
                { name: "isnull1", expr: { is_null: { lit: { null: true } } } },
                { name: "tb1", expr: { time_between: [{ lit: { int: 10 } }, { lit: { int: 15 } }] } },
                { name: "in1", expr: { in: { needle: { lit: { string: "a" } }, haystack: { arr: { items: [{ lit: { string: "a" } }, { lit: { string: "b" } }] } } } } },
                { name: "map1", expr: { map_enum: { expr: { var: { row: { field: "state" } } }, mapping: { new: 1, done: 2 } } } },
                { name: "len1", expr: { call: { fn: "len", args: [{ lit: { string: "abcd" } }] } } },
                { name: "str1", expr: { call: { fn: "str", args: [{ lit: { int: 12 } }] } } },
                { name: "int1", expr: { call: { fn: "int", args: [{ lit: { string: "42" } }] } } },
                { name: "float1", expr: { call: { fn: "float", args: [{ lit: { string: "3.5" } }] } } },
                {
                  name: "get1",
                  expr: {
                    get: {
                      expr: { var: { row: { field: "attrs_json" } } },
                      path: "foo.bar",
                    },
                  },
                },
                {
                  name: "has1",
                  expr: {
                    has: {
                      expr: { var: { row: { field: "attrs_json" } } },
                      path: "foo.bar",
                    },
                  },
                },
              ],
            },
          },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = {
        now: 1,
        actor: "u",
        snap: () => [
          {
            entity_id: "a",
            state: "new",
            attrs_json: JSON.stringify({ foo: { bar: 7 }, s: "12", n: 3 }),
            severity_i: 2,
            created_at: 5,
            updated_ts: 1,
          },
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
            len: (v: any) => (Array.isArray(v) ? v.length : typeof v === "string" ? v.length : v && typeof v === "object" ? Object.keys(v).length : 0),
            str: (v: any) => (v === null ? null : String(v)),
            int: (v: any) => (typeof v === "number" ? Math.trunc(v) : typeof v === "string" ? Number.parseInt(v, 10) : null),
            float: (v: any) => (typeof v === "number" ? v : typeof v === "string" ? Number.parseFloat(v) : null),
          },
        },
      }

      const oracle = interpretQuery(q, ctx)
      const normalizeBools = (rows: any[]) =>
        rows.map((r) =>
          Object.fromEntries(
            Object.entries(r).map(([k, v]) => [k, typeof v === "boolean" ? (v ? 1 : 0) : v])
          )
        )

      assert.deepEqual(canonRows(normalizeBools(sqlRows)), canonRows(normalizeBools(oracle.rows as any[])))
    } finally {
      db.close()
    }
  })
})
