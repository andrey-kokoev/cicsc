import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { SqliteD1Adapter } from "../../adapters/sqlite/src/adapter"

type EventRow = {
  tenant_id: string
  entity_type: string
  entity_id: string
  seq: number
}

type FakeStmt = {
  sql: string
  binds: any[]
}

function makeConcurrentFakeDb () {
  const events: EventRow[] = []
  let txLocked = false
  const waiters: Array<() => void> = []

  function unlockTx () {
    txLocked = false
    const next = waiters.shift()
    if (next) next()
  }

  async function lockTx () {
    if (!txLocked) {
      txLocked = true
      return
    }
    await new Promise<void>((resolve) => waiters.push(resolve))
    txLocked = true
  }

  return {
    events,
    db: {
      prepare (sql: string) {
        return {
          bind (...binds: any[]) {
            return { sql, binds } as FakeStmt
          },
        }
      },
      async batch (stmts: any[]) {
        const stmt = (stmts[0] ?? {}) as FakeStmt
        const sql = String(stmt.sql ?? "")
        const binds = stmt.binds ?? []

        if (sql === "BEGIN IMMEDIATE") {
          await lockTx()
          return [{ success: true, results: [] }]
        }
        if (sql === "COMMIT" || sql === "ROLLBACK") {
          unlockTx()
          return [{ success: true, results: [] }]
        }

        if (sql.includes("SELECT result_json FROM command_receipts")) {
          return [{ success: true, results: [] }]
        }

        if (sql.includes("SELECT active_version FROM tenant_versions")) {
          return [{ success: true, results: [{ active_version: 0 }] }]
        }

        if (sql.includes("SELECT COALESCE(MAX(seq), 0) AS max_seq")) {
          const [tenant_id, entity_type, entity_id] = binds.map(String)
          const max = events
            .filter((e) => e.tenant_id === tenant_id && e.entity_type === entity_type && e.entity_id === entity_id)
            .reduce((m, e) => Math.max(m, e.seq), 0)
          return [{ success: true, results: [{ max_seq: max }] }]
        }

        if (sql.includes("INSERT INTO events_v0")) {
          for (let i = 0; i < binds.length; i += 8) {
            events.push({
              tenant_id: String(binds[i + 0]),
              entity_type: String(binds[i + 1]),
              entity_id: String(binds[i + 2]),
              seq: Number(binds[i + 3]),
            })
          }
          return [{ success: true, results: [] }]
        }

        return [{ success: true, results: [] }]
      },
      async exec (_sql: string) {
        return { ok: true }
      },
    },
  }
}

describe("concurrency stress", () => {
  it("allocates unique ordered seq under conflicting commands on same entity", async () => {
    const fake = makeConcurrentFakeDb()
    const adapter = new SqliteD1Adapter(fake.db as any)

    const N = 40
    const outs = await Promise.all(
      Array.from({ length: N }, (_, i) =>
        adapter.append_events({
          tenant_id: "t",
          entity_type: "Ticket",
          entity_id: "E1",
          command_id: `c-${i}`,
          events: [{ event_type: "x", payload: {}, ts: i + 1, actor_id: "u" }],
        })
      )
    )

    const seqs = outs.map((o) => o.seq_from).sort((a, b) => a - b)
    assert.deepEqual(seqs, Array.from({ length: N }, (_, i) => i + 1))
  })

  it("isolates seq streams across entities under concurrent load", async () => {
    const fake = makeConcurrentFakeDb()
    const adapter = new SqliteD1Adapter(fake.db as any)

    const N = 20
    await Promise.all([
      ...Array.from({ length: N }, (_, i) =>
        adapter.append_events({
          tenant_id: "t",
          entity_type: "Ticket",
          entity_id: "E1",
          command_id: `e1-${i}`,
          events: [{ event_type: "x", payload: {}, ts: i + 1, actor_id: "u" }],
        })
      ),
      ...Array.from({ length: N }, (_, i) =>
        adapter.append_events({
          tenant_id: "t",
          entity_type: "Ticket",
          entity_id: "E2",
          command_id: `e2-${i}`,
          events: [{ event_type: "x", payload: {}, ts: i + 1, actor_id: "u" }],
        })
      ),
    ])

    const e1 = fake.events.filter((e) => e.entity_id === "E1").map((e) => e.seq).sort((a, b) => a - b)
    const e2 = fake.events.filter((e) => e.entity_id === "E2").map((e) => e.seq).sort((a, b) => a - b)
    assert.deepEqual(e1, Array.from({ length: N }, (_, i) => i + 1))
    assert.deepEqual(e2, Array.from({ length: N }, (_, i) => i + 1))
  })
})
