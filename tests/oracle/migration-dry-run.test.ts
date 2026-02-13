import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { runMigrationDryRun } from "../../core/runtime/migration-dry-run"
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

describe("migration dry-run artifacts", () => {
  it("produces a passing dry-run artifact and writes it to sink", async () => {
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

    let written: any = null
    const report = await runMigrationDryRun({
      from_bundle,
      to_bundle,
      migration_id: "v0_to_v1",
      events,
      now: 2,
      actor: "u1",
      intrinsics,
      write_artifact: (a) => { written = a },
    })

    assert.equal(report.ok, true)
    assert.equal(report.artifact.version, "cicsc/migration-dry-run-v1")
    assert.equal(report.artifact.source_events, 1)
    assert.equal(report.artifact.migrated_events, 1)
    assert.equal(written?.migration_id, "v0_to_v1")
    assert.equal(written?.ok, true)
  })

  it("produces a failing dry-run artifact when preflight fails", async () => {
    const { from_bundle, to_bundle } = bundlesForTicketMigration()
    const badEvents: Event[] = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        seq: 2, // gap -> integrity failure
        event_type: "ticket_created",
        payload: {},
        ts: 2,
        actor_id: "u1",
      },
    ]

    const report = await runMigrationDryRun({
      from_bundle,
      to_bundle,
      migration_id: "v0_to_v1",
      events: badEvents,
      now: 2,
      actor: "u1",
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.equal(report.artifact.ok, false)
    assert.equal(report.artifact.preflight.checks.history_integrity.ok, false)
    assert.match(
      report.artifact.preflight.checks.history_integrity.detail ?? "",
      /missing sequence/i
    )
  })
})
