import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { preflightMigration } from "../../core/runtime/migration-preflight"
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

function bundlesForTicketMigration () {
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

  return { from_bundle, to_bundle }
}

describe("migration preflight checklist", () => {
  it("passes all checks for valid migration/bundles/history", () => {
    const { from_bundle, to_bundle } = bundlesForTicketMigration()
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

    const report = preflightMigration({
      from_bundle,
      to_bundle,
      migration_id: "v0_to_v1",
      events,
      now: 2,
      actor: "u1",
      intrinsics,
    })

    assert.equal(report.ok, true)
    assert.equal(report.checks.from_bundle_valid.ok, true)
    assert.equal(report.checks.to_bundle_valid.ok, true)
    assert.equal(report.checks.migration_exists.ok, true)
    assert.equal(report.checks.version_forward.ok, true)
    assert.equal(report.checks.history_integrity.ok, true)
    assert.equal(report.checks.replay_verification.ok, true)
  })

  it("fails preflight when history integrity has seq gaps", () => {
    const { from_bundle, to_bundle } = bundlesForTicketMigration()
    const events: Event[] = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        seq: 2,
        event_type: "ticket_created",
        payload: {},
        ts: 2,
        actor_id: "u1",
      },
    ]

    const report = preflightMigration({
      from_bundle,
      to_bundle,
      migration_id: "v0_to_v1",
      events,
      now: 3,
      actor: "u1",
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.equal(report.checks.history_integrity.ok, false)
    assert.match(report.checks.history_integrity.detail ?? "", /missing sequence/i)
  })

  it("fails preflight when migration version is not forward", () => {
    const { from_bundle } = bundlesForTicketMigration()
    const to_bundle = {
      core_ir: {
        ...((from_bundle as any).core_ir),
        migrations: {
          bad_migration: {
            from_version: 2,
            to_version: 1,
            on_type: "Ticket",
            event_transforms: {},
          },
        },
      },
    }

    const report = preflightMigration({
      from_bundle,
      to_bundle,
      migration_id: "bad_migration",
      events: [],
      now: 1,
      actor: "u1",
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.equal(report.checks.version_forward.ok, false)
    assert.match(report.checks.version_forward.detail ?? "", /non-forward migration/i)
  })
})
