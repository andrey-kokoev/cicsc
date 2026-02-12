import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { SqliteD1Adapter } from "../../adapters/sqlite/src/adapter"

type FakeStmt = { sql: string; binds: any[] }

function makeFakeDb (opts?: { failSqlIncludes?: string }) {
  const sqlLog: string[] = []

  return {
    sqlLog,
    db: {
      prepare (sql: string) {
        return {
          bind (...binds: any[]) {
            return { sql, binds } satisfies FakeStmt
          },
        }
      },
      async batch<T = unknown> (stmts: any[]): Promise<any[]> {
        const out: any[] = []
        for (const stmt of stmts as FakeStmt[]) {
          const sql = stmt.sql
          sqlLog.push(sql)

          if (opts?.failSqlIncludes && sql.includes(opts.failSqlIncludes)) {
            out.push({ success: false, error: "forced failure" })
            continue
          }

          if (sql.includes("SELECT active_version FROM tenant_versions")) {
            out.push({ success: true, results: [{ active_version: 0 }] })
            continue
          }

          if (sql.includes("SELECT result_json FROM command_receipts")) {
            out.push({ success: true, results: [] })
            continue
          }

          if (sql.includes("SELECT COALESCE(MAX(seq), 0) AS max_seq")) {
            out.push({ success: true, results: [{ max_seq: 10 }] })
            continue
          }

          out.push({ success: true, results: [] })
        }
        return out as T[]
      },
      async exec (_sql: string): Promise<any> {
        return { count: 0, duration: 0 }
      },
    },
  }
}

describe("sqlite adapter tx boundary", () => {
  it("wraps set_active_version in BEGIN IMMEDIATE/COMMIT", async () => {
    const fake = makeFakeDb()
    const adapter = new SqliteD1Adapter(fake.db as any)

    await adapter.set_active_version("t", 3)

    assert.equal(fake.sqlLog[0], "BEGIN IMMEDIATE")
    assert.equal(fake.sqlLog[fake.sqlLog.length - 1], "COMMIT")
    assert.equal(fake.sqlLog.includes("ROLLBACK"), false)
  })

  it("wraps append_events in BEGIN IMMEDIATE/COMMIT", async () => {
    const fake = makeFakeDb()
    const adapter = new SqliteD1Adapter(fake.db as any)

    const out = await adapter.append_events({
      tenant_id: "t",
      entity_type: "Ticket",
      entity_id: "e1",
      command_id: "cmd1",
      events: [
        { event_type: "created", payload: { x: 1 }, ts: 1, actor_id: "u" },
        { event_type: "tagged", payload: { y: 2 }, ts: 2, actor_id: "u" },
      ],
    })

    assert.deepEqual(out, { entity_id: "e1", seq_from: 11, seq_to: 12 })
    assert.equal(fake.sqlLog[0], "BEGIN IMMEDIATE")
    assert.equal(fake.sqlLog[fake.sqlLog.length - 1], "COMMIT")
    assert.equal(fake.sqlLog.includes("ROLLBACK"), false)
  })

  it("rolls back when a statement fails inside append_events", async () => {
    const fake = makeFakeDb({ failSqlIncludes: "INSERT INTO events_v0" })
    const adapter = new SqliteD1Adapter(fake.db as any)

    await assert.rejects(async () => {
      await adapter.append_events({
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        command_id: "cmd1",
        events: [{ event_type: "created", payload: {}, ts: 1, actor_id: "u" }],
      })
    })

    assert.equal(fake.sqlLog[0], "BEGIN IMMEDIATE")
    assert.equal(fake.sqlLog.includes("ROLLBACK"), true)
    assert.equal(fake.sqlLog.includes("COMMIT"), false)
  })
})
