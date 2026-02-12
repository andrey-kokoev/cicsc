import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { verifyHistoryAgainstIr, verifyHistoryAgainstIrStream } from "../../core/runtime/verify"
import type { Event } from "../../core/runtime/replay"
import type { VmIntrinsics } from "../../core/vm/eval"

const intrinsics: VmIntrinsics = {
  has_role: () => false,
  role_of: () => "user",
  auth_ok: () => true,
  constraint: () => true,
  len: () => null,
  str: (v) => (v == null ? null : String(v)),
  int: () => null,
  float: () => null,
}

async function *toAsync (events: Event[]): AsyncGenerator<Event> {
  for (const e of events) yield e
}

describe("streaming verifier", () => {
  it("matches non-stream verification outcome", async () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new", "open"],
            initial_state: "new",
            attrs: {},
            commands: {},
            reducer: {
              created: [{ set_state: { expr: { lit: { string: "open" } } } }],
            },
          },
        },
      },
    }

    const events: Event[] = [
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 1, event_type: "created", payload: {}, ts: 1, actor_id: "u" },
      { tenant_id: "t", entity_type: "Ticket", entity_id: "B", seq: 1, event_type: "created", payload: {}, ts: 2, actor_id: "u" },
    ]

    const normal = verifyHistoryAgainstIr({
      bundle,
      events,
      now: 3,
      actor: "u",
      intrinsics,
    })

    const streamed = await verifyHistoryAgainstIrStream({
      bundle,
      events: toAsync(events),
      now: 3,
      actor: "u",
      intrinsics,
    })

    assert.equal(streamed.ok, normal.ok)
    assert.equal(streamed.entities_count, normal.entities_count)
    assert.equal(streamed.events_count, normal.events_count)
  })

  it("enforces max entity bound", async () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            commands: {},
            reducer: { created: [] },
          },
        },
      },
    }

    const events: Event[] = [
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 1, event_type: "created", payload: {}, ts: 1, actor_id: "u" },
      { tenant_id: "t", entity_type: "Ticket", entity_id: "B", seq: 1, event_type: "created", payload: {}, ts: 2, actor_id: "u" },
    ]

    const streamed = await verifyHistoryAgainstIrStream({
      bundle,
      events: toAsync(events),
      now: 3,
      actor: "u",
      intrinsics,
      max_entities: 1,
    })

    assert.equal(streamed.ok, false)
    assert.ok(streamed.violations.some((v) => v.message.includes("max_entities")))
  })
})
