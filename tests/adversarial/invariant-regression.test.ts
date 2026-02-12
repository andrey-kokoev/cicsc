import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { typecheckSpecV0 } from "../../spec/typecheck"
import { compileSpecToBundleV0 } from "../../runtime/http/compile"
import { verifyMigrationReplay } from "../../core/runtime/migration-verify"
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

describe("invariant regression suite", () => {
  it("rejects known-bad spec: missing reducer for emitted event", () => {
    const out = typecheckSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          commands: {
            create: { emit: [{ type: "created", payload: {} }] },
          },
          reducers: {},
        },
      },
    } as any)

    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.message.includes("missing reducer")))
  })

  it("rejects known-bad spec at compile: invalid initial state", () => {
    assert.throws(
      () =>
        compileSpecToBundleV0({
          version: 0,
          entities: {
            Ticket: {
              id: "string",
              states: ["new"],
              initial: "done",
              commands: {},
              reducers: {},
            },
          },
        }),
      /spec typecheck failed/
    )
  })

  it("rejects known-bad migration: target bundle missing declared migration id", () => {
    const bundle: any = {
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
      migration_id: "v0_to_v1",
      events: [],
      now: 1,
      actor: "u",
      intrinsics,
    })

    assert.equal(report.ok, false)
    assert.match(report.error ?? "", /missing migration/)
  })
})
