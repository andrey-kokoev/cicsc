import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { typecheckSpecV0 } from "../../spec/typecheck"
import { verifyMigrationReplay } from "../../core/runtime/migration-verify"
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

describe("migration fault injection", () => {
  it("rejects partial event transforms at spec typecheck", () => {
    const out = typecheckSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["open"],
          initial: "open",
          commands: {
            create: { emit: [{ type: "created", payload: {} }] },
            close: { emit: [{ type: "closed", payload: {} }] },
          },
          reducers: { created: [], closed: [] },
        },
      },
      migrations: {
        m0_to_1: {
          from: 0,
          to: 1,
          entity: "Ticket",
          event_transforms: { created: { emit_as: "created_v2" } },
          state_map: { open: "open" },
        },
      },
    } as any)

    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.message.includes("missing transform")))
  })

  it("fails migration verification when target bundle schema is invalid", () => {
    const from_bundle: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["open"],
            initial_state: "open",
            attrs: {},
            commands: {},
            reducer: { created: [] },
          },
        },
      },
    }
    const bad_to_bundle: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            // invalid on purpose: id_type mismatch
            id_type: "int",
            states: ["open"],
            initial_state: "open",
            attrs: {},
            commands: {},
            reducer: { created_v2: [] },
          },
        },
        migrations: {
          m0_to_1: {
            from_version: 0,
            to_version: 1,
            on_type: "Ticket",
            event_transforms: { created: { emit_as: "created_v2" } },
          },
        },
      },
    }

    const report = verifyMigrationReplay({
      from_bundle,
      to_bundle: bad_to_bundle,
      migration_id: "m0_to_1",
      events: [],
      now: 1,
      actor: "u",
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.match(report.error ?? "", /to_bundle invalid/)
  })

  it("fails when migrated history violates target replay constraints", () => {
    const from_bundle: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new", "done"],
            initial_state: "new",
            attrs: {},
            commands: {},
            reducer: { closed: [{ set_state: { expr: { lit: { string: "done" } } } }] },
          },
        },
      },
    }
    const to_bundle: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new", "done"],
            initial_state: "new",
            attrs: {},
            commands: {},
            reducer: { closed_v2: [{ set_state: { expr: { lit: { string: "done" } } } }] },
          },
        },
        constraints: {
          no_done: {
            kind: "snapshot",
            on_type: "Ticket",
            expr: {
              ne: [
                { var: { row: { field: "state" } } },
                { lit: { string: "done" } },
              ],
            },
          },
        },
        migrations: {
          m0_to_1: {
            from_version: 0,
            to_version: 1,
            on_type: "Ticket",
            event_transforms: { closed: { emit_as: "closed_v2" } },
          },
        },
      },
    }

    const events: Event[] = [{
      tenant_id: "t",
      entity_type: "Ticket",
      entity_id: "A",
      seq: 1,
      event_type: "closed",
      payload: {},
      ts: 1,
      actor_id: "u",
    }]

    const report = verifyMigrationReplay({
      from_bundle,
      to_bundle,
      migration_id: "m0_to_1",
      events,
      now: 2,
      actor: "u",
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.equal(report.target_verify.ok, false)
  })
})
