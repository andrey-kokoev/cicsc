import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { installSqliteSchemaV0, openSqliteMemory } from "../harness/sqlite-memory"

describe("perf: sqlite explain-plan checks", () => {
  it("uses indexes for indexed snapshot filter paths", () => {
    let db: ReturnType<typeof openSqliteMemory> | null = null
    try {
      db = openSqliteMemory()
    } catch {
      return
    }

    try {
      installSqliteSchemaV0(db)

      const insert = db.prepare(
        `INSERT INTO snapshots_v0(tenant_id, entity_type, entity_id, state, attrs_json, updated_ts, severity_i, created_at)
         VALUES(?,?,?,?,?,?,?,?)`
      )
      for (let i = 0; i < 1000; i++) {
        insert.run([
          "t",
          "Ticket",
          `e${i}`,
          i % 2 === 0 ? "new" : "triage",
          "{}",
          i,
          i % 5,
          i,
        ])
      }

      const q: any = {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          { filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } },
          { limit: 50 },
        ],
      }

      const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
      const explainRows = db.prepare(`EXPLAIN QUERY PLAN ${plan.sql}`).all(["t", "Ticket", ...plan.binds]) as any[]
      const details = explainRows.map((r) => String(r.detail ?? "")).join("\n")

      assert.match(details, /USING (COVERING )?INDEX/i)
      assert.doesNotMatch(details, /SCAN .*snapshots_v0/i)
    } finally {
      db.close()
    }
  })
})
