import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { typecheckCoreIrV0 } from "../../core/ir/typecheck"

describe("view row_policy typing", () => {
  it("rejects illegal row fields in row_policy", () => {
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
        board: {
          kind: "metric",
          on_type: "Ticket",
          query: { source: { snap: { type: "Ticket" } }, pipeline: [] },
          row_policy: {
            eq: [{ var: { row: { field: "owner_id" } } }, { var: { actor: true } }],
          },
        } as any,
      },
    } as any)

    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.path.includes("row_policy")))
  })
})
