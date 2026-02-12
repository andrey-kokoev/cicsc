import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { transformHistoryWithMigration } from "../../core/runtime/migrate"
import { replayAllEntities, type Event } from "../../core/runtime/replay"
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

describe("migration conformance (oracle replay before/after)", () => {
  it("preserves replayed semantics under event/state mapping", () => {
    const from_ir = {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new", "open"],
          initial_state: "new",
          attrs: {},
          commands: {},
          reducer: {
            ticket_created: [{ set_state: { expr: { lit: { string: "open" } } } }],
          },
        },
      },
    } as any

    const to_ir = {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new", "active"],
          initial_state: "new",
          attrs: {},
          commands: {},
          reducer: {
            ticket_opened: [{ set_state: { expr: { lit: { string: "active" } } } }],
          },
        },
      },
    } as any

    const migration = {
      from_version: 0,
      to_version: 1,
      on_type: "Ticket",
      event_transforms: {
        ticket_created: { emit_as: "ticket_opened" },
      },
      state_map: {
        new: "new",
        open: "active",
      },
    } as any

    const sourceEvents: Event[] = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "A",
        seq: 1,
        event_type: "ticket_created",
        payload: {},
        ts: 1,
        actor_id: "u",
      },
    ]

    const before = replayAllEntities({
      inputs: { ir: from_ir, intrinsics },
      events: sourceEvents,
    })

    const migratedEvents = transformHistoryWithMigration({
      migration,
      events: sourceEvents,
      intrinsics,
    })

    const after = replayAllEntities({
      inputs: { ir: to_ir, intrinsics },
      events: migratedEvents,
    })

    const beforeSnap = before.get("Ticket::A")!
    const afterSnap = after.get("Ticket::A")!

    assert.equal(migration.state_map[beforeSnap.state], afterSnap.state)
    assert.deepEqual(afterSnap.attrs, beforeSnap.attrs)
  })

  it("preserves replayed semantics when migration drops explicitly ignored events", () => {
    const from_ir = {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new", "open"],
          initial_state: "new",
          attrs: {},
          commands: {},
          reducer: {
            ticket_created: [{ set_state: { expr: { lit: { string: "open" } } } }],
            ticket_pinged: [],
          },
        },
      },
    } as any

    const to_ir = {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new", "active"],
          initial_state: "new",
          attrs: {},
          commands: {},
          reducer: {
            ticket_opened: [{ set_state: { expr: { lit: { string: "active" } } } }],
          },
        },
      },
    } as any

    const migration = {
      from_version: 0,
      to_version: 1,
      on_type: "Ticket",
      event_transforms: {
        ticket_created: { emit_as: "ticket_opened" },
        ticket_pinged: { drop: true },
      },
      state_map: {
        new: "new",
        open: "active",
      },
    } as any

    const sourceEvents: Event[] = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "A",
        seq: 1,
        event_type: "ticket_created",
        payload: {},
        ts: 1,
        actor_id: "u",
      },
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "A",
        seq: 2,
        event_type: "ticket_pinged",
        payload: {},
        ts: 2,
        actor_id: "u",
      },
    ]

    const before = replayAllEntities({
      inputs: { ir: from_ir, intrinsics },
      events: sourceEvents,
    })

    const migratedEvents = transformHistoryWithMigration({
      migration,
      events: sourceEvents,
      intrinsics,
    })

    const after = replayAllEntities({
      inputs: { ir: to_ir, intrinsics },
      events: migratedEvents,
    })

    const beforeSnap = before.get("Ticket::A")!
    const afterSnap = after.get("Ticket::A")!

    assert.equal(migration.state_map[beforeSnap.state], afterSnap.state)
    assert.deepEqual(afterSnap.attrs, beforeSnap.attrs)
    assert.equal(migratedEvents.some((e) => e.event_type === "ticket_pinged"), false)
  })
})
