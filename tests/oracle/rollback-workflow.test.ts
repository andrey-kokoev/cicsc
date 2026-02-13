import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { rollbackMigrationChain } from "../../core/runtime/rollback"
import type { Event } from "../../core/runtime/replay"
import type { VmIntrinsics } from "../../core/vm/eval"

const intrinsics: VmIntrinsics = {
  has_role: () => false,
  role_of: () => "user",
  auth_ok: () => true,
  constraint: () => true,
  len: (v) => (Array.isArray(v) || typeof v === "string" ? v.length : null),
  str: (v) => (v == null ? null : String(v)),
  int: (v) => (typeof v === "number" ? Math.trunc(v) : null),
  float: (v) => (typeof v === "number" ? v : null),
}

function bundleWithMigration (eventTransforms: any) {
  return {
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
            ticket_created: [{ set_state: { expr: { lit: { string: "open" } } } }],
            ticket_opened: [{ set_state: { expr: { lit: { string: "open" } } } }],
          },
        },
      },
      migrations: {
        v0_to_v1: {
          from_version: 0,
          to_version: 1,
          on_type: "Ticket",
          event_transforms: eventTransforms,
        },
      },
    },
  }
}

describe("rollback workflow (reversible subset)", () => {
  it("rolls back history when migration is reversible", () => {
    const to_bundle = bundleWithMigration({
      ticket_created: { emit_as: "ticket_opened" },
    })
    const events: Event[] = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        seq: 1,
        event_type: "ticket_opened",
        payload: {},
        ts: 1,
        actor_id: "u1",
      },
    ]

    const report = rollbackMigrationChain({
      to_bundle,
      migration_id: "v0_to_v1",
      events,
      intrinsics,
    })

    assert.equal(report.ok, true)
    assert.equal(report.events?.[0]?.event_type, "ticket_created")
  })

  it("fails rollback when migration has drops", () => {
    const to_bundle = bundleWithMigration({
      ticket_created: { drop: true },
    })

    const report = rollbackMigrationChain({
      to_bundle,
      migration_id: "v0_to_v1",
      events: [],
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.match(report.error ?? "", /dropped event/i)
  })

  it("fails rollback when migration has payload_map", () => {
    const to_bundle = bundleWithMigration({
      ticket_created: { emit_as: "ticket_opened", payload_map: { x: { lit: { int: 1 } } } },
    })

    const report = rollbackMigrationChain({
      to_bundle,
      migration_id: "v0_to_v1",
      events: [],
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.match(report.error ?? "", /payload_map/i)
  })

  it("fails rollback when event mapping is non-injective", () => {
    const to_bundle = bundleWithMigration({
      ticket_created: { emit_as: "ticket_event" },
      ticket_reopened: { emit_as: "ticket_event" },
    })

    const report = rollbackMigrationChain({
      to_bundle,
      migration_id: "v0_to_v1",
      events: [],
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.match(report.error ?? "", /non-injective event mapping/i)
  })
})
