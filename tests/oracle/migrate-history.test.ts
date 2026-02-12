import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { transformHistoryWithMigration } from "../../core/runtime/migrate"
import type { Event } from "../../core/runtime/replay"
import type { VmIntrinsics } from "../../core/vm/eval"

const intrinsics: VmIntrinsics = {
  has_role: () => false,
  role_of: () => "user",
  auth_ok: () => true,
  constraint: () => true,
  len: (v) => (Array.isArray(v) || typeof v === "string" ? v.length : null),
  str: (v) => (v == null ? null : String(v)),
  int: (v) => {
    if (typeof v === "number") return Math.trunc(v)
    if (typeof v === "string" && v.trim() !== "") {
      const n = Number(v)
      return Number.isFinite(n) ? Math.trunc(n) : null
    }
    return null
  },
  float: (v) => {
    if (typeof v === "number") return v
    if (typeof v === "string" && v.trim() !== "") {
      const n = Number(v)
      return Number.isFinite(n) ? n : null
    }
    return null
  },
}

describe("history migration transformer", () => {
  it("rewrites event types and payload via Expr payload_map", () => {
    const events: Event[] = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        seq: 1,
        event_type: "ticket_created",
        payload: { title: "A" },
        ts: 10,
        actor_id: "u1",
      },
    ]

    const out = transformHistoryWithMigration({
      migration: {
        from_version: 0,
        to_version: 1,
        on_type: "Ticket",
        event_transforms: {
          ticket_created: {
            emit_as: "ticket_opened",
            payload_map: {
              subject: { var: { e_payload: { path: "title" } } },
            },
          },
        },
      },
      events,
      intrinsics,
    })

    assert.equal(out.length, 1)
    assert.equal(out[0]!.event_type, "ticket_opened")
    assert.deepEqual(out[0]!.payload, { subject: "A" })
    assert.equal(out[0]!.seq, 1)
  })

  it("drops mapped events and resequences remaining stream", () => {
    const events: Event[] = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        seq: 1,
        event_type: "noop",
        payload: {},
        ts: 10,
        actor_id: "u1",
      },
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        seq: 2,
        event_type: "kept",
        payload: {},
        ts: 11,
        actor_id: "u1",
      },
    ]

    const out = transformHistoryWithMigration({
      migration: {
        from_version: 0,
        to_version: 1,
        on_type: "Ticket",
        event_transforms: {
          noop: { drop: true },
        },
      },
      events,
      intrinsics,
    })

    assert.equal(out.length, 1)
    assert.equal(out[0]!.event_type, "kept")
    assert.equal(out[0]!.seq, 1)
  })
})
