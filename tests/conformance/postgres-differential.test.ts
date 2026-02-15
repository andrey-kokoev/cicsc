import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql as lowerPg } from "../../adapters/postgres/src/lower/query-to-sql"
import { openPgMemory, installPostgresSchemaV0, runLoweredQueryPlan as runPgPlan, upsertSnapshot as upsertPgSnapshot } from "../harness/pg-memory"

describe("postgres-differential conformance (BE3.1)", () => {
  it("matches Postgres execution against oracle for complex expressions", async (t) => {
    let pg: any
    try {
      pg = await openPgMemory()
    } catch (e: any) {
      t.skip(`postgres harness setup failed: ${e.message}`)
      return
    }

    try {
      await installPostgresSchemaV0(pg.pool)

      const rows = [
        { entity_id: "t1", state: "Open", severity: 10, updated_ts: 100 },
        { entity_id: "t2", state: "Closed", severity: 5, updated_ts: 200 },
      ]

      for (const r of rows) {
        await upsertPgSnapshot(pg.pool, {
          tenant_id: "test-tenant",
          entity_type: "Ticket",
          state: r.state,
          updated_ts: r.updated_ts,
          attrs: { severity: r.severity },
          severity: r.severity // shadow
        })
      }

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          { filter: { gt: [{ var: { row: { field: "severity" } } }, { lit: { int: 7 } }] } },
          { project: { fields: [{ name: "id", expr: { var: { row: { field: "entity_id" } } } }] } }
        ]
      }

      const pgRows = await runPgPlan(pg.pool, {
        tenant_id: "test-tenant",
        query: q,
        plan: lowerPg(q, { version: 0, tenant_id: "test-tenant" })
      })

      const oracleRows = interpretQuery(q, {
        now: 1,
        actor: "u",
        snap: () => rows.map(r => ({ entity_id: r.entity_id, state: r.state, updated_ts: r.updated_ts, attrs: { severity: r.severity }, shadows: { severity: r.severity } })),
        sla_status: () => [],
        baseEnv: { now: 1, actor: "u", state: "", input: {}, attrs: {}, row: {}, arg: {}, intrinsics: {} as any }
      }).rows

      assert.equal(pgRows.length, oracleRows.length)
      assert.deepEqual(pgRows[0].id, oracleRows[0].entity_id)

    } finally {
      await pg.pool.end()
    }
  })
})
