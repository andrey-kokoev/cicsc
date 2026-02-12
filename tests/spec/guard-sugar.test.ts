import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"
import type { SpecV0 } from "../../spec/ast"

function mk (when: any): SpecV0 {
  return {
    version: 0,
    entities: {
      Ticket: {
        id: "string",
        states: ["new", "done"],
        initial: "new",
        attributes: {},
        commands: {
          close: {
            when,
            emit: [{ type: "closed", payload: {} }],
          },
        },
        reducers: { closed: [] },
      },
    },
  }
}

describe("spec guard sugar", () => {
  it("lowers state_is + role_is guard sugar into boolean expr", () => {
    const ir = compileSpecV0ToCoreIr(
      mk({
        state_is: "new",
        role_is: "agent",
      })
    )

    const guard = (ir.types.Ticket.commands as any).close.guard.expr
    assert.deepEqual(guard, {
      and: [
        { eq: [{ var: { state: true } }, { lit: { string: "new" } }] },
        {
          call: {
            fn: "has_role",
            args: [{ var: { actor: true } }, { lit: { string: "agent" } }],
          },
        },
      ],
    })
  })

  it("supports nested any/all sugar", () => {
    const ir = compileSpecV0ToCoreIr(
      mk({
        any: [
          { state_is: "new" },
          { all: [{ role_is: "agent" }, { state_is: "done" }] },
        ],
      })
    )

    const guard = (ir.types.Ticket.commands as any).close.guard.expr
    assert.ok(guard.or)
    assert.equal(Array.isArray(guard.or), true)
    assert.equal(guard.or.length, 2)
  })
})
