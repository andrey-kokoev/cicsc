import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("spec to IR compiler", () => {
  it("lowers DSL spec into typed Core IR bundle", () => {
    const bundle = compileSpecToBundleV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new", "triage", "done"],
          initial: "new",
          attributes: {
            title: { type: "string" },
          },
          shadows: {
            severity_i: { type: "int" },
          },
          commands: {
            create: {
              inputs: {
                title: { type: "string" },
              },
              when: { state_is: "new" },
              emit: [
                {
                  type: "created",
                  payload: {
                    title: { var: { input: { field: "title" } } },
                  },
                },
              ],
            },
          },
          reducers: {
            created: [
              { set_attr: { field: "title", value: { var: { e_payload: { path: "title" } } } } },
            ],
          },
        },
      },
      constraints: {
        no_done_as_new: {
          kind: "snapshot",
          entity: "Ticket",
          when: { ne: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] },
        },
      },
      views: {
        board: {
          kind: "lanes",
          on: "Ticket",
          lanes: {
            states: ["new", "triage"],
            order_by: { field: "updated_ts", dir: "desc" },
            limit: 25,
          },
        },
      },
    })

    const ir: any = bundle.core_ir
    assert.equal(ir.version, 0)
    assert.ok(ir.types.Ticket)
    assert.ok(ir.types.Ticket.commands.create)
    assert.ok(ir.constraints.no_done_as_new)
    assert.ok(ir.views.board)
  })
})
