import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { verifyMigrationReplay } from "../../core/runtime/migration-verify"
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

describe("migration replay verification", () => {
  it("verifies migrated history against target bundle", () => {
    const from_bundle = {
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
            },
          },
        },
      },
    }

    const to_bundle = {
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
              ticket_opened: [{ set_state: { expr: { lit: { string: "open" } } } }],
            },
          },
        },
        migrations: {
          v0_to_v1: {
            from_version: 0,
            to_version: 1,
            on_type: "Ticket",
            event_transforms: {
              ticket_created: { emit_as: "ticket_opened" },
            },
          },
        },
      },
    }

    const events: Event[] = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        seq: 1,
        event_type: "ticket_created",
        payload: {},
        ts: 1,
        actor_id: "u1",
      },
    ]

    const report = verifyMigrationReplay({
      from_bundle,
      to_bundle,
      migration_id: "v0_to_v1",
      events,
      now: 2,
      actor: "u1",
      intrinsics,
    })

    assert.equal(report.ok, true)
    assert.equal(report.source_verify.ok, true)
    assert.equal(report.target_verify.ok, true)
    assert.equal(report.migrated_events, 1)
  })

  it("fails when migration id is missing", () => {
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
            reducer: {},
          },
        },
      },
    }

    const report = verifyMigrationReplay({
      from_bundle: bundle,
      to_bundle: bundle,
      migration_id: "missing",
      events: [],
      now: 1,
      actor: "u",
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.match(report.error ?? "", /missing migration/)
  })
})
