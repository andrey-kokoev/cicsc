import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { compileSurfaceToIr } from "../../spec/compile-surface"
import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"
import { parseSpecV0 } from "../../spec/parse-yaml"

describe("Surface DSL Roundtrip", () => {
  it("produces identical IR for explicit and sugared forms", () => {
    const cicsc = `
entity Ticket:
  states: [Open, Closed]
  command Resolve:
    when state is Open
    `
    const yaml = {
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["Open", "Closed"],
          initial: "Open",
          commands: {
            Resolve: {
              when: { eq: [{ var: { state: true } }, { lit: { string: "Open" } }] },
              emit: [{ type: "Resolveed", payload: {} }]
            }
          }
        }
      }
    }

    const irFromCicsc = compileSurfaceToIr(cicsc)
    const irFromYaml = compileSpecV0ToCoreIr(parseSpecV0(yaml))

    // Compare essential parts
    assert.deepEqual(irFromCicsc.types.Ticket.states, irFromYaml.types.Ticket.states)
    assert.deepEqual(irFromCicsc.types.Ticket.commands.Resolve.guard, irFromYaml.types.Ticket.commands.Resolve.guard)
    assert.deepEqual(irFromCicsc.types.Ticket.commands.Resolve.emits, irFromYaml.types.Ticket.commands.Resolve.emits)
  })
})
