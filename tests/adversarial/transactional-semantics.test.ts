import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { withImmediateTx } from "../../adapters/sqlite/src/tx"
import { SqliteD1Adapter } from "../../adapters/sqlite/src/adapter"
import { replayAllEntities, type Event } from "../../core/runtime/replay"
import type { VmIntrinsics } from "../../core/vm/eval"

describe("adversarial transactional semantics", () => {
  it("rolls back when transaction crashes mid-tx", async () => {
    const log: string[] = []
    const db = {
      prepare (sql: string) {
        return {
          bind (..._args: any[]) {
            return { sql }
          },
        }
      },
      async batch (stmts: any[]) {
        const sql = String(stmts[0]?.sql ?? "")
        log.push(sql)
        if (sql.includes("INSERT INTO crash_here")) {
          return [{ success: false, error: "forced crash" }]
        }
        return [{ success: true, results: [] }]
      },
    }

    await assert.rejects(async () => {
      await withImmediateTx(db as any, async (tx) => {
        await tx.exec("INSERT INTO before_crash VALUES(1)")
        await tx.exec("INSERT INTO crash_here VALUES(1)")
      })
    }, /forced crash/)

    assert.equal(log[0], "BEGIN IMMEDIATE")
    assert.equal(log.includes("ROLLBACK"), true)
    assert.equal(log.includes("COMMIT"), false)
  })

  it("short-circuits duplicate command submissions via existing receipt", async () => {
    let insertEventsCalls = 0
    const db = {
      prepare (sql: string) {
        return {
          bind (..._binds: any[]) {
            return { sql }
          },
        }
      },
      async batch (stmts: any[]) {
        const sql = String(stmts[0]?.sql ?? "")
        if (sql.includes("SELECT result_json FROM command_receipts")) {
          return [{ success: true, results: [{ result_json: JSON.stringify({ entity_id: "e1", seq_from: 1, seq_to: 1 }) }] }]
        }
        if (sql.includes("INSERT INTO events_v0")) insertEventsCalls++
        return [{ success: true, results: [] }]
      },
      async exec (_sql: string) {
        return { ok: true }
      },
    }

    const adapter = new SqliteD1Adapter(db as any)
    const out = await adapter.append_events({
      tenant_id: "t",
      entity_type: "Ticket",
      entity_id: "e1",
      command_id: "dup-cmd",
      events: [{ event_type: "created", payload: {}, ts: 1, actor_id: "u" }],
    })

    assert.deepEqual(out, { entity_id: "e1", seq_from: 1, seq_to: 1 })
    assert.equal(insertEventsCalls, 0)
  })

  it("replays deterministically with out-of-order event input", () => {
    const ir: any = {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new", "done"],
          initial_state: "new",
          attrs: {},
          commands: {},
          reducer: {
            closed: [{ set_state: { expr: { lit: { string: "done" } } } }],
          },
        },
      },
    }
    const intrinsics: VmIntrinsics = {
      has_role: () => true,
      role_of: () => "user",
      auth_ok: () => true,
      constraint: () => true,
      len: () => null,
      str: (v: any) => (v == null ? null : String(v)),
      int: () => null,
      float: () => null,
    }

    const events: Event[] = [
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 2, event_type: "closed", payload: {}, ts: 2, actor_id: "u" },
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 1, event_type: "closed", payload: {}, ts: 1, actor_id: "u" },
    ]

    const out = replayAllEntities({
      inputs: { ir, intrinsics },
      events,
    })

    const snap = out.get("Ticket::A")!
    assert.equal(snap.state, "done")
  })
})
