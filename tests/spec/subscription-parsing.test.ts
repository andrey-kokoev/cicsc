
import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { parseDSL } from "../../spec/parse-dsl"
import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"

describe("Subscription Parsing", () => {
  it("should parse subscription from DSL", () => {
    const dsl = `
entity Ticket:
  states: [Open, Closed]
  attr assignee: string

subscription MySub:
  on Ticket
  filter assignee eq me
`
    const spec = parseDSL(dsl)
    assert.ok(spec.subscriptions)
    assert.deepEqual(spec.subscriptions?.MySub, {
      on: "Ticket",
      filter: {
        field: "assignee",
        op: "eq",
        value: { var: "me" }
      }
    })

    const ir = compileSpecV0ToCoreIr(spec)
    assert.ok(ir.subscriptions?.MySub)
    assert.equal(ir.subscriptions?.MySub.on_type, "Ticket")
    assert.deepEqual(ir.subscriptions?.MySub.filter, {
      eq: [
        { var: { attrs: { field: "assignee" } } },
        { var: { actor: true } }
      ]
    })
  })
})
