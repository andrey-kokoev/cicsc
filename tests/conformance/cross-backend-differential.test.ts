import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql as lowerSqlite } from "../../adapters/sqlite/src/lower/query-to-sql"
import { lowerQueryToSql as lowerPg } from "../../adapters/postgres/src/lower/query-to-sql"

import {
  installSqliteSchemaV0,
  openSqliteMemory,
  runLoweredQueryPlan as runSqlitePlan,
  upsertSnapshot as upsertSqliteSnapshot,
} from "../harness/sqlite-memory"
import {
  installPostgresSchemaV0,
  openPgMemory,
  runLoweredQueryPlan as runPgPlan,
  upsertSnapshot as upsertPgSnapshot,
} from "../harness/pg-memory"

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

describe("cross-backend differential conformance", () => {
  it("matches SQLite and Postgres execution against oracle semantics", async (t) => {
    let sqliteDb: any
    let pg: any
    try {
      sqliteDb = openSqliteMemory()
      pg = await openPgMemory()
    } catch (e: any) {
      t.skip(`backend harness missing dependency: ${e?.message ?? String(e)}`)
      return
    }

    try {
      installSqliteSchemaV0(sqliteDb)
      await installPostgresSchemaV0(pg.pool)

      const rows = [
        { entity_id: "a", state: "new", severity_i: 2, created_at: 10 },
        { entity_id: "b", state: "triage", severity_i: 3, created_at: 5 },
        { entity_id: "c", state: "new", severity_i: 1, created_at: 1 },
      ]

      for (const r of rows) {
        upsertSqliteSnapshot(sqliteDb, { tenant_id: "t", entity_type: "Ticket", attrs: {}, updated_ts: 1, ...r })
        await upsertPgSnapshot(pg.pool, { tenant_id: "t", entity_type: "Ticket", attrs: {}, updated_ts: 1, ...r })
      }

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          { filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } },
          {
            project: {
              fields: [
                { name: "id", expr: { var: { row: { field: "entity_id" } } } },
                { name: "sev", expr: { var: { row: { field: "severity_i" } } } },
              ],
            },
          },
          { order_by: [{ expr: { var: { row: { field: "sev" } } }, dir: "desc" }] },
        ],
      }

      const sqliteRows = runSqlitePlan(sqliteDb, {
        tenant_id: "t",
        query: q,
        plan: lowerSqlite(q, { version: 0, tenant_id: "t" }),
      }).map((r: any) => ({ id: r.id, sev: r.sev }))

      const pgRows = (await runPgPlan(pg.pool, {
        tenant_id: "t",
        query: q,
        plan: lowerPg(q, { version: 0, tenant_id: "t" }),
      })).map((r: any) => ({ id: r.id, sev: r.sev }))

      const oracle = interpretQuery(q, {
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
            str: (v: any) => (v == null ? null : String(v)),
            int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
            float: (v: any) => (typeof v === "number" ? v : null),
          },
        },
      }).rows

      assert.deepEqual(canonRows(sqliteRows), canonRows(oracle))
      assert.deepEqual(canonRows(pgRows), canonRows(oracle))
      assert.deepEqual(canonRows(pgRows), canonRows(sqliteRows))
    } finally {
      sqliteDb?.close?.()
      await pg?.close?.()
    }
  })
})
