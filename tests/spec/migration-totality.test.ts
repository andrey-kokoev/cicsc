import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { typecheckSpecV0 } from "../../spec/typecheck"

describe("migration totality/executability", () => {
  it("rejects partial event transform coverage", () => {
    const out = typecheckSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["open", "closed"],
          initial: "open",
          commands: {
            c1: { emit: [{ type: "created", payload: {} }] },
            c2: { emit: [{ type: "closed", payload: {} }] },
          },
          reducers: {
            created: [{ set_state: "open" }],
            closed: [{ set_state: "closed" }],
          },
        },
      },
      migrations: {
        m0_to_1: {
          from: 0,
          to: 1,
          entity: "Ticket",
          event_transforms: {
            created: { emit_as: "created_v2" },
          },
          state_map: {
            open: "open",
            closed: "closed",
          },
        },
      },
    } as any)

    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.message.includes("missing transform for emitted event 'closed'")))
  })

  it("rejects partial state mapping", () => {
    const out = typecheckSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["open", "closed"],
          initial: "open",
          commands: {
            c: { emit: [{ type: "created", payload: {} }] },
          },
          reducers: {
            created: [{ set_state: "open" }],
          },
        },
      },
      migrations: {
        m0_to_1: {
          from: 0,
          to: 1,
          entity: "Ticket",
          event_transforms: {
            created: { emit_as: "created_v2" },
          },
          state_map: {
            open: "open",
          },
        },
      },
    } as any)

    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.message.includes("missing state mapping for 'closed'")))
  })
})
