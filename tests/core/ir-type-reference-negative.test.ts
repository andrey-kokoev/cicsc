import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { typecheckCoreIrV0 } from "../../core/ir/typecheck"

describe("core typechecker: fail-fast unknown type references", () => {
  it("rejects view.on_type when type is missing", () => {
    const out = typecheckCoreIrV0({
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
      views: {
        bad_view: {
          kind: "metric",
          on_type: "MissingType",
          query: { source: { snap: { type: "Ticket" } }, pipeline: [] },
        } as any,
      },
    } as any)

    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.code === "UNKNOWN_TYPE" && e.path === "views.bad_view.on_type"))
  })

  it("rejects bool_query constraint on missing type", () => {
    const out = typecheckCoreIrV0({
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
      constraints: {
        bad_constraint: {
          kind: "bool_query",
          on_type: "MissingType",
          args: {},
          query: { source: { snap: { type: "Ticket" } }, pipeline: [] },
          assert: { ge: [{ var: { rows_count: true } }, { lit: { int: 0 } }] },
        },
      },
    } as any)

    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.code === "UNKNOWN_TYPE" && e.path === "constraints.bad_constraint.on_type"))
  })
})
