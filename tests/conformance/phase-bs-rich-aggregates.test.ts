// /tests/conformance/phase-bs-rich-aggregates.test.ts
// BS2.3: Oracle conformance tests for rate, ratio, time_between aggregations

import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { installSqliteSchemaV0, openSqliteMemory, runLoweredQueryPlan, upsertSnapshot } from "../harness/sqlite-memory"

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

function makeCtx (snapRows: any[]) {
  return {
    now: 1000,
    actor: "u",
    snap: () => snapRows,
    sla_status: () => [],
    baseEnv: {
      now: 1000,
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

describe("conformance: BS rich aggregates (rate, ratio, time_between)", () => {
  it("exec lowered query with rate aggregation equals oracle", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      // Insert test data: tickets with response time and resolution time
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "resolved", attrs: {}, updated_ts: 1, response_ts: 100, resolve_ts: 500 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "resolved", attrs: {}, updated_ts: 1, response_ts: 200, resolve_ts: 800 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "open", attrs: {}, updated_ts: 1, response_ts: 300, resolve_ts: null })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          {
            group_by: {
              keys: [{ name: "state", expr: { var: { row: { field: "state" } } } }],
              aggs: {
                resolution_rate: {
                  rate: {
                    numerator: { var: { row: { field: "resolve_ts" } } },
                    denominator: { var: { row: { field: "response_ts" } } },
                    unit: "per_hour",
                  },
                },
              },
            },
          },
          { order_by: [{ expr: { var: { row: { field: "state" } } }, dir: "asc" }] },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = makeCtx([
        { entity_id: "a", state: "resolved", response_ts: 100, resolve_ts: 500 },
        { entity_id: "b", state: "resolved", response_ts: 200, resolve_ts: 800 },
        { entity_id: "c", state: "open", response_ts: 300, resolve_ts: null },
      ])

      const oracle = interpretQuery(q, ctx)
      const sqlProjected = sqlRows.map((r: any) => ({ state: r.state, resolution_rate: r.resolution_rate }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })

  it("exec lowered query with ratio aggregation equals oracle", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1, completed: 1, total: 10 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1, completed: 2, total: 10 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1, completed: 0, total: 5 })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          {
            group_by: {
              keys: [{ name: "state", expr: { var: { row: { field: "state" } } } }],
              aggs: {
                completion_pct: {
                  ratio: {
                    numerator: { var: { row: { field: "completed" } } },
                    denominator: { var: { row: { field: "total" } } },
                    scale: 100,
                  },
                },
              },
            },
          },
          { order_by: [{ expr: { var: { row: { field: "state" } } }, dir: "asc" }] },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = makeCtx([
        { entity_id: "a", state: "new", completed: 1, total: 10 },
        { entity_id: "b", state: "new", completed: 2, total: 10 },
        { entity_id: "c", state: "triage", completed: 0, total: 5 },
      ])

      const oracle = interpretQuery(q, ctx)
      const sqlProjected = sqlRows.map((r: any) => ({ state: r.state, completion_pct: r.completion_pct }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })

  it("exec lowered query with time_between aggregation equals oracle", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      // Tickets with created and resolved timestamps
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "resolved", attrs: {}, updated_ts: 1, created_ts: 0, resolved_ts: 3600 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "resolved", attrs: {}, updated_ts: 1, created_ts: 0, resolved_ts: 7200 })
      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "open", attrs: {}, updated_ts: 1, created_ts: 0, resolved_ts: null })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          {
            group_by: {
              keys: [{ name: "state", expr: { var: { row: { field: "state" } } } }],
              aggs: {
                avg_resolution_hours: {
                  time_between: {
                    start_expr: { var: { row: { field: "created_ts" } } },
                    end_expr: { var: { row: { field: "resolved_ts" } } },
                    unit: "hours",
                  },
                },
              },
            },
          },
          { order_by: [{ expr: { var: { row: { field: "state" } } }, dir: "asc" }] },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = makeCtx([
        { entity_id: "a", state: "resolved", created_ts: 0, resolved_ts: 3600 },
        { entity_id: "b", state: "resolved", created_ts: 0, resolved_ts: 7200 },
        { entity_id: "c", state: "open", created_ts: 0, resolved_ts: null },
      ])

      const oracle = interpretQuery(q, ctx)
      const sqlProjected = sqlRows.map((r: any) => ({ state: r.state, avg_resolution_hours: r.avg_resolution_hours }))
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
    } finally {
      db.close()
    }
  })

  it("handles zero denominator in rate and ratio gracefully", () => {
    const db = openSqliteMemory()
    try {
      installSqliteSchemaV0(db)

      upsertSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1, value: 10, zero_col: 0 })

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          {
            group_by: {
              keys: [{ name: "state", expr: { var: { row: { field: "state" } } } }],
              aggs: {
                zero_rate: {
                  rate: {
                    numerator: { var: { row: { field: "value" } } },
                    denominator: { var: { row: { field: "zero_col" } } },
                    unit: "per_second",
                  },
                },
                zero_ratio: {
                  ratio: {
                    numerator: { var: { row: { field: "value" } } },
                    denominator: { var: { row: { field: "zero_col" } } },
                    scale: 1,
                  },
                },
              },
            },
          },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query: q, plan })

      const ctx: any = makeCtx([
        { entity_id: "a", state: "new", value: 10, zero_col: 0 },
      ])

      const oracle = interpretQuery(q, ctx)
      
      // Both should return null when denominator is zero
      assert.equal(sqlRows[0]?.zero_rate, null)
      assert.equal(sqlRows[0]?.zero_ratio, null)
      assert.equal(oracle.rows[0]?.zero_rate, null)
      assert.equal(oracle.rows[0]?.zero_ratio, null)
    } finally {
      db.close()
    }
  })
})
