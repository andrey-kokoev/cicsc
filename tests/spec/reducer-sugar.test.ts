import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"
import type { SpecV0 } from "../../spec/ast"

describe("spec reducer sugar", () => {
  it("lowers reducer shorthand into core reducer ops", () => {
    const spec: SpecV0 = {
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new", "done"],
          initial: "new",
          attributes: { title: { type: "string" } },
          shadows: { severity_i: { type: "int" } },
          commands: {
            c: { emit: [{ type: "created", payload: {} }] },
          },
          reducers: {
            created: [
              { set_state: "done" } as any,
              { set_attr: { field: "title", value: "hello" } } as any,
              { set_shadow: { field: "severity_i", value: 3 } } as any,
              { clear_attr: "title" } as any,
            ],
          },
        },
      },
    }

    const ir = compileSpecV0ToCoreIr(spec)
    const ops = (ir.types.Ticket.reducer as any).created

    assert.deepEqual(ops[0], { set_state: { expr: { lit: { string: "done" } } } })
    assert.deepEqual(ops[1], { set_attr: { name: "title", expr: { lit: { string: "hello" } } } })
    assert.deepEqual(ops[2], { set_shadow: { name: "severity_i", expr: { lit: { int: 3 } } } })
    assert.deepEqual(ops[3], { clear_attr: { name: "title" } })
  })
})
