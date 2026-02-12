import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("migration compiler", () => {
  it("lowers spec migration declarations into Core IR migrations", () => {
    const bundle = compileSpecToBundleV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["open"],
          initial: "open",
          commands: {},
          reducers: {},
        },
      },
      migrations: {
        ticket_v0_to_v1: {
          from: 0,
          to: 1,
          entity: "Ticket",
          event_transforms: {
            ticket_created: {
              emit_as: "ticket_opened",
              payload_map: {
                title: { var: { e_payload: { path: "title" } } },
              },
            },
          },
          state_map: {
            open: "open",
          },
        },
      },
    })

    const mig: any = bundle.core_ir.migrations?.ticket_v0_to_v1
    assert.ok(mig)
    assert.equal(mig.from_version, 0)
    assert.equal(mig.to_version, 1)
    assert.equal(mig.on_type, "Ticket")
    assert.equal(mig.event_transforms.ticket_created.emit_as, "ticket_opened")
  })

  it("rejects non-adjacent migration versions", () => {
    assert.throws(
      () =>
        compileSpecToBundleV0({
          version: 0,
          entities: {
            Ticket: {
              id: "string",
              states: ["open"],
              initial: "open",
              commands: {},
              reducers: {},
            },
          },
          migrations: {
            bad_edge: {
              from: 0,
              to: 2,
              entity: "Ticket",
              event_transforms: {},
            },
          },
        }),
      /from N to N\+1/
    )
  })
})
