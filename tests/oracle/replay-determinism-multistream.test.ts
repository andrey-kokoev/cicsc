import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { replayAllEntities } from "../../core/runtime/replay"
import type { VmIntrinsics } from "../../core/vm/eval"

const intrinsics: VmIntrinsics = {
  has_role: () => true,
  role_of: () => "agent",
  auth_ok: () => true,
  constraint: () => true,
  len: () => 0,
  str: (v) => (v == null ? null : String(v)),
  int: (v) => (typeof v === "number" ? Math.trunc(v) : null),
  float: (v) => (typeof v === "number" ? v : null),
}

describe("oracle replay determinism across representative streams", () => {
  const ir: any = {
    version: 0,
    types: {
      Ticket: {
        id_type: "string",
        states: ["new", "triage", "closed"],
        initial_state: "new",
        attrs: {},
        commands: {},
        reducer: {
          created: [],
          triaged: [{ set_state: { expr: { lit: { string: "triage" } } } }],
          closed: [{ set_state: { expr: { lit: { string: "closed" } } } }],
        },
      },
    },
  }

  const events: any[] = [
    { tenant_id: "t", entity_type: "Ticket", entity_id: "B", seq: 2, event_type: "triaged", payload: {}, ts: 20, actor_id: "u" },
    { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 1, event_type: "created", payload: {}, ts: 10, actor_id: "u" },
    { tenant_id: "t", entity_type: "Ticket", entity_id: "B", seq: 1, event_type: "created", payload: {}, ts: 11, actor_id: "u" },
    { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 2, event_type: "closed", payload: {}, ts: 21, actor_id: "u" },
  ]

  it("is deterministic under repeated evaluation of the same mixed history", () => {
    const run1 = replayAllEntities({ inputs: { ir, intrinsics }, events })
    const run2 = replayAllEntities({ inputs: { ir, intrinsics }, events })

    assert.deepEqual(Array.from(run1.entries()), Array.from(run2.entries()))
  })

  it("preserves per-stream isolation for same-type interleaved entities", () => {
    const out = replayAllEntities({ inputs: { ir, intrinsics }, events })

    const a = out.get("Ticket::A")
    const b = out.get("Ticket::B")

    assert.ok(a)
    assert.ok(b)
    assert.equal(a!.state, "closed")
    assert.equal(b!.state, "triage")
  })
})
