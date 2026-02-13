import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { parseSpecV0 } from "../../spec/parse-yaml"
import { typecheckSpecV0 } from "../../spec/typecheck"

describe("phase8 DSL ergonomics negative coverage", () => {
  it("rejects duplicate state names with path-qualified diagnostic", () => {
    const spec = parseSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new", "new"],
          initial: "new",
          attributes: {},
          commands: {
            c: { emit: [{ type: "created", payload: {} }] },
          },
          reducers: { created: [] },
        },
      },
    })
    const out = typecheckSpecV0(spec)
    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.path === "entities.Ticket.states" && e.message.includes("duplicate state")))
  })

  it("rejects duplicate emitted events in one command", () => {
    const spec = parseSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          attributes: {},
          commands: {
            c: {
              emit: [
                { type: "created", payload: {} },
                { type: "created", payload: {} },
              ],
            },
          },
          reducers: { created: [] },
        },
      },
    })
    const out = typecheckSpecV0(spec)
    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.path === "entities.Ticket.commands.c.emit" && e.message.includes("duplicate emitted event")))
  })
})
