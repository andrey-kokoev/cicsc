import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { openSqliteMemory, installSqliteSchemaV0 } from "../harness/sqlite-memory"

describe("perf: sqlite large snapshot tables", () => {
  it("keeps indexed query latency bounded on large snapshot table", () => {
    let db: ReturnType<typeof openSqliteMemory> | null = null
    try {
      db = openSqliteMemory()
    } catch {
      // Environment dependency gate (better-sqlite3) is optional in this repo.
      return
    }

    try {
      installSqliteSchemaV0(db)

      const insert = db.prepare(
        `INSERT INTO snapshots_v0(tenant_id, entity_type, entity_id, state, attrs_json, updated_ts, severity_i, created_at)
         VALUES(?,?,?,?,?,?,?,?)`
      )

      const total = 20000
      for (let i = 0; i < total; i++) {
        insert.run([
          "t",
          "Ticket",
          `e${i}`,
          i % 3 === 0 ? "new" : "triage",
          "{}",
          i,
          (i % 5) + 1,
          i,
        ])
      }

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          { filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } },
          { order_by: [{ expr: { var: { row: { field: "created_at" } } }, dir: "desc" }] },
          { limit: 100 },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const sql = db.prepare(plan.sql)

      const runs: number[] = []
      for (let i = 0; i < 8; i++) {
        const t0 = Date.now()
        const out = sql.all(["t", "Ticket", ...plan.binds])
        const t1 = Date.now()
        runs.push(t1 - t0)
        assert.ok(Array.isArray(out))
      }

      const worstMs = Math.max(...runs)
      const maxMs = Number(process.env.CICSC_PERF_MAX_MS ?? 2500)
      assert.ok(
        worstMs <= maxMs,
        `worst query latency ${worstMs}ms exceeded bound ${maxMs}ms`
      )
    } finally {
      db.close()
    }
  })
})
