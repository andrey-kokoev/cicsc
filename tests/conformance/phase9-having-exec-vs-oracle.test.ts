import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql as lowerSqliteQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { lowerQueryToSql as lowerPostgresQueryToSql } from "../../adapters/postgres/src/lower/query-to-sql"
import { installSqliteSchemaV0, openSqliteMemory, runLoweredQueryPlan as runSqlitePlan, upsertSnapshot as upsertSqliteSnapshot } from "../harness/sqlite-memory"
import { installPostgresSchemaV0, openPgMemory, runLoweredQueryPlan as runPostgresPlan, upsertSnapshot as upsertPgSnapshot } from "../harness/pg-memory"

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

function oracleCtx (rows: any[]): any {
  return {
    now: 1,
    actor: "u",
    snap: () => rows,
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

const qHaving: any = {
  source: { snap: { type: "Ticket" } },
  pipeline: [
    {
      group_by: {
        keys: [{ name: "state", expr: { var: { row: { field: "state" } } } }],
        aggs: { cnt: { count: {} } },
      },
    },
    { having: { gt: [{ var: { row: { field: "cnt" } } }, { lit: { int: 1 } }] } },
    { order_by: [{ expr: { var: { row: { field: "state" } } }, dir: "asc" }] },
  ],
}

const snapRows = [
  { entity_id: "a", state: "new", updated_ts: 1, severity_i: 1, created_at: 1 },
  { entity_id: "b", state: "new", updated_ts: 1, severity_i: 2, created_at: 2 },
  { entity_id: "c", state: "triage", updated_ts: 1, severity_i: 2, created_at: 3 },
]

describe("phase9 having differential", () => {
  it("sqlite execution with HAVING matches oracle", () => {
    const db = openSqliteMemory()
    installSqliteSchemaV0(db)

    upsertSqliteSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1, severity_i: 1, created_at: 1 })
    upsertSqliteSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1, severity_i: 2, created_at: 2 })
    upsertSqliteSnapshot(db, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1, severity_i: 2, created_at: 3 })

    const plan = lowerSqliteQueryToSql(qHaving, { version: 0, tenant_id: "t" })
    const sqlRows = runSqlitePlan(db, { tenant_id: "t", query: qHaving, plan })
    const oracle = interpretQuery(qHaving, oracleCtx(snapRows))

    const projected = sqlRows.map((r: any) => ({ state: r.state, cnt: r.cnt }))
    assert.deepEqual(canonRows(projected), canonRows(oracle.rows))
  })

  it.skip("postgres execution with HAVING matches oracle (pg-mem planner limitation; tracked in Z2)", async () => {
    const pg = await openPgMemory()
    try {
      await installPostgresSchemaV0(pg.pool)
      await upsertPgSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "a", state: "new", attrs: {}, updated_ts: 1, severity_i: 1, created_at: 1 })
      await upsertPgSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "b", state: "new", attrs: {}, updated_ts: 1, severity_i: 2, created_at: 2 })
      await upsertPgSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", entity_id: "c", state: "triage", attrs: {}, updated_ts: 1, severity_i: 2, created_at: 3 })

      const plan = lowerPostgresQueryToSql(qHaving, { version: 0, tenant_id: "t" })
      const sqlRows = await runPostgresPlan(pg.pool, { tenant_id: "t", query: qHaving, plan })
      const oracle = interpretQuery(qHaving, oracleCtx(snapRows))

      const projected = sqlRows.map((r: any) => ({ state: r.state, cnt: r.cnt }))
      assert.deepEqual(canonRows(projected), canonRows(oracle.rows))
    } finally {
      await pg.close()
    }
  })
})
