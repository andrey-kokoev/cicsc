import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { parseSpecV0 } from "../../spec/parse-yaml"

describe("spec migration shape", () => {
  it("accepts v0 migration declarations in DSL shape", () => {
    const spec: any = parseSpecV0({
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
        m0_to_1: {
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

    assert.equal(spec.migrations?.m0_to_1?.from, 0)
    assert.equal(spec.migrations?.m0_to_1?.to, 1)
    assert.equal(spec.migrations?.m0_to_1?.entity, "Ticket")
  })
})
