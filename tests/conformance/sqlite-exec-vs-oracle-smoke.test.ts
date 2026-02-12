// /tests/conformance/sqlite-exec-vs-oracle-smoke.test.ts

import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { lowerBoolQueryConstraintToSql } from "../../adapters/sqlite/src/lower/constraint-to-sql"
import { installSqliteSchemaV0, openSqliteMemory, runLoweredQueryPlan, runPlanAll, upsertSnapshot } from "../harness/sqlite-memory"

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

function oracleCtx (snapRows: any[]) {
  return {
    now: 1,
    actor: "u",
    snap: () => snapRows,
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
}

describe("conformance: sqlite execution vs oracle (smoke)", () => {
  it("exec lowered bool_query constraint equals oracle truth", () => {
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

      const plan = lowerBoolQueryConstraintToSql({ constraint, version: 0, tenant_id: "t", args: { limit: 2 } })
      const row = runPlanAll(db, plan.sql, plan.binds)[0]
      assert.ok(row)
      const okSql = row.ok === 1 || row.ok === true

      const qOut = interpretQuery(constraint.query, oracleCtx([
        { entity_id: "a", state: "new" },
        { entity_id: "b", state: "new" },
        { entity_id: "c", state: "triage" },
      ]) as any)
      const okOracle = qOut.rows_count <= 2

      assert.equal(okSql, okOracle)
    } finally {
      db.close()
    }
  })

  it("exec lowered query group_by rows equals oracle rows", () => {
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
      const sqlProjected = sqlRows.map((r: any) => ({ state: r.state, rows_count: r.rows_count, sev_sum: r.sev_sum }))

      const oracle = interpretQuery(q, oracleCtx([
        { entity_id: "a", state: "new", severity_i: 2 },
        { entity_id: "b", state: "new", severity_i: 3 },
        { entity_id: "c", state: "triage", severity_i: 1 },
      ]) as any)

      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })
})
