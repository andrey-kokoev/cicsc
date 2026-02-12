import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { parseSpecV0 } from "../../spec/parse-yaml"
import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"

describe("spec DSL shape", () => {
  it("accepts DSL shape using entities (distinct from IR types)", () => {
    const spec = parseSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          attributes: {},
          commands: {
            create: {
              inputs: {},
              when: { lit: { bool: true } },
              emit: [{ type: "created", payload: {} }],
            },
          },
          reducers: {
            created: [],
          },
        },
      },
    })

    const ir = compileSpecV0ToCoreIr(spec)
    assert.ok(ir.types.Ticket)
    assert.equal(ir.types.Ticket.id_type, "string")
    assert.ok(ir.types.Ticket.commands.create)
  })

  it("rejects IR-shaped spec payloads that use types", () => {
    assert.throws(
      () =>
        parseSpecV0({
          version: 0,
          types: {},
        }),
      /entities/
    )
  })
})
