import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"
import type { SpecV0 } from "../../spec/ast"

describe("spec view sugar", () => {
  it("lowers lanes/order/limit sugar into query pipeline", () => {
    const spec: SpecV0 = {
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new", "triage", "done"],
          initial: "new",
          attributes: {},
          commands: { c: { emit: [{ type: "created", payload: {} }] } },
          reducers: { created: [] },
        },
      },
      views: {
        board: {
          kind: "lanes",
          on: "Ticket",
          lanes: {
            states: ["new", "triage"],
            order_by: { field: "created_at", dir: "desc" },
            limit: 50,
          },
        },
      },
    }

    const ir = compileSpecV0ToCoreIr(spec)
    const q: any = (ir.views as any).board.query

    assert.deepEqual(q.source, { snap: { type: "Ticket" } })
    assert.equal(Array.isArray(q.pipeline), true)
    assert.equal(q.pipeline.length, 3)
    assert.deepEqual(q.pipeline[2], { limit: 50 })
  })
})
