import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { SqliteD1Adapter } from "../../../adapters/sqlite/src/adapter"

type FakeStmt = { sql: string; binds: any[] }

function makeFakeDb (opts?: {
  failSqlIncludes?: string,
  results?: Record<string, any[]>
}) {
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

          let found = false
          if (opts?.results) {
            for (const [key, res] of Object.entries(opts.results)) {
              if (sql.includes(key)) {
                out.push({ success: true, results: res })
                found = true
                break
              }
            }
          }

          if (!found) {
            out.push({ success: true, results: [] })
          }
        }
        return out as T[]
      },
      async exec (_sql: string): Promise<any> {
        return { count: 0, duration: 0 }
      },
    },
  }
}

describe("SqliteD1Adapter Queue Methods", () => {
  it("enqueues message with correct SQL", async () => {
    const fake = makeFakeDb()
    const adapter = new SqliteD1Adapter(fake.db as any)

    await adapter.enqueue({
      tenant_id: "t1",
      queue_name: "test_queue",
      message: { foo: "bar" },
      idempotency_key: "idem1"
    })

    assert.ok(fake.sqlLog.some(sql => sql.includes("INSERT INTO queue_test_queue")))
    assert.ok(fake.sqlLog.some(sql => sql.includes("message_json")))
  })

  it("dequeues message transactionally", async () => {
    const fake = makeFakeDb({
      results: {
        "SELECT id, message_json": [{ id: "m1", message_json: '{"ok":true}', attempts: 0, created_at: 100 }]
      }
    })
    const adapter = new SqliteD1Adapter(fake.db as any)

    const msg = await adapter.dequeue({
      tenant_id: "t1",
      queue_name: "test_queue",
      visibility_timeout_ms: 30000
    })

    assert.equal(msg?.id, "m1")
    assert.deepEqual(msg?.payload, { ok: true })

    assert.equal(fake.sqlLog[0], "BEGIN IMMEDIATE")
    assert.ok(fake.sqlLog.some(sql => sql.includes("UPDATE queue_test_queue")))
    assert.ok(fake.sqlLog.includes("COMMIT"))
  })

  it("acks message by deleting", async () => {
    const fake = makeFakeDb()
    const adapter = new SqliteD1Adapter(fake.db as any)

    await adapter.ack({
      tenant_id: "t1",
      queue_name: "test_queue",
      message_id: "m1"
    })

    assert.ok(fake.sqlLog.some(sql => sql.includes("DELETE FROM queue_test_queue")))
  })
})
