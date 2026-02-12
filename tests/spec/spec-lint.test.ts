import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { lintSpecV0 } from "../../spec/lint"

describe("spec linter", () => {
  it("detects unreachable states and dead commands", () => {
    const res = lintSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new", "active", "done", "ghost"],
          initial: "new",
          attributes: {},
          commands: {
            start: { when: { state_is: "new" }, emit: [{ type: "started", payload: {} }] },
            finish: { when: { state_is: "active" }, emit: [{ type: "finished", payload: {} }] },
            reopen: { when: { state_is: "ghost" }, emit: [{ type: "reopened", payload: {} }] },
          },
          reducers: {
            started: [{ set_state: "active" }],
            finished: [{ set_state: "done" }],
            reopened: [{ set_state: "active" }],
          },
        },
      },
    })

    assert.ok(res.issues.some((i) => i.code === "UNREACHABLE_STATE" && i.message.includes("ghost")))
    assert.ok(res.issues.some((i) => i.code === "DEAD_COMMAND" && i.path.endsWith(".reopen")))
  })

  it("detects anti-pattern commands", () => {
    const res = lintSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new", "active"],
          initial: "new",
          attributes: {},
          commands: {
            noisy: {
              emit: [{ type: "a", payload: {} }, { type: "b", payload: {} }],
            },
          },
          reducers: {
            a: [{ set_state: "active" }, { set_state: "new" }],
            b: [],
          },
        },
      },
    })

    assert.ok(res.issues.some((i) => i.code === "ANTI_PATTERN_UNSCOPED_COMMAND"))
    assert.ok(res.issues.some((i) => i.code === "ANTI_PATTERN_MULTI_EMIT"))
    assert.ok(res.issues.some((i) => i.code === "ANTI_PATTERN_MULTIPLE_STATE_WRITES"))
  })
})
