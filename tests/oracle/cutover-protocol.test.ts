import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { cutoverPauseMigrateResume } from "../../core/runtime/cutover"
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

describe("cutover protocol", () => {
  it("runs pause->verify/migrate->activate->resume flow", async () => {
    const order: string[] = []
    const source: Event[] = [
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

    let activeVersion = 0
    const written: Event[][] = []

    const report = await cutoverPauseMigrateResume({
      tenant_id: "t",
      migration_id: "v0_to_v1",
      from_bundle,
      to_bundle,
      now: 10,
      actor: "u1",
      intrinsics,
      pause_tenant: async () => { order.push("pause") },
      resume_tenant: async () => { order.push("resume") },
      load_source_history: async () => {
        order.push("load")
        return source
      },
      write_target_history: async (events) => {
        order.push("write")
        written.push(events)
      },
      set_active_version: async (_tenant_id, version) => {
        order.push("activate")
        activeVersion = version
      },
    })

    assert.equal(report.ok, true)
    assert.equal(activeVersion, 1)
    assert.equal(written.length, 1)
    assert.equal(written[0]![0]!.event_type, "ticket_opened")
    assert.ok(report.boundaries.paused_at > 0)
    assert.ok((report.boundaries.verified_at ?? 0) >= report.boundaries.paused_at)
    assert.ok((report.boundaries.switched_at ?? 0) >= (report.boundaries.verified_at ?? 0))
    assert.ok(report.boundaries.resumed_at >= (report.boundaries.switched_at ?? 0))
    assert.deepEqual(order, ["pause", "load", "write", "activate", "resume"])
  })

  it("resumes tenant even when verification fails", async () => {
    const order: string[] = []
    const bad_to_bundle = { ...to_bundle, core_ir: { ...to_bundle.core_ir, migrations: {} } }

    const report = await cutoverPauseMigrateResume({
      tenant_id: "t",
      migration_id: "v0_to_v1",
      from_bundle,
      to_bundle: bad_to_bundle,
      now: 10,
      actor: "u1",
      intrinsics,
      pause_tenant: async () => { order.push("pause") },
      resume_tenant: async () => { order.push("resume") },
      load_source_history: async () => {
        order.push("load")
        return []
      },
      write_target_history: async () => { order.push("write") },
      set_active_version: async () => { order.push("activate") },
    })

    assert.equal(report.ok, false)
    assert.ok(report.boundaries.paused_at > 0)
    assert.ok(report.boundaries.resumed_at >= report.boundaries.paused_at)
    assert.deepEqual(order, ["pause", "load", "resume"])
  })
})
