import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecToBundleV0, CompileDiagnosticsError } from "../../runtime/http/compile"

function expectCompileFailure (spec: any): CompileDiagnosticsError {
  try {
    compileSpecToBundleV0(spec)
    assert.fail("expected compile to fail")
  } catch (e: any) {
    assert.ok(e instanceof CompileDiagnosticsError)
    return e
  }
}

describe("spec negative tests: invariant-weakening patterns", () => {
  it("rejects non-adjacent migration versions", () => {
    const err = expectCompileFailure({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          attributes: {},
          commands: { c: { emit: [{ type: "created", payload: {} }] } },
          reducers: { created: [] },
        },
      },
      migrations: {
        m0_to_2: {
          from: 0,
          to: 2,
          entity: "Ticket",
          event_transforms: { created: { emit_as: "created_v2" } },
          state_map: { new: "new" },
        },
      },
    })
    assert.ok(err.diagnostics.some((d) => d.path === "migrations.m0_to_2"))
  })

  it("rejects migration missing transforms for emitted events", () => {
    const err = expectCompileFailure({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          attributes: {},
          commands: { c: { emit: [{ type: "created", payload: {} }] } },
          reducers: { created: [] },
        },
      },
      migrations: {
        m0_to_1: {
          from: 0,
          to: 1,
          entity: "Ticket",
          event_transforms: {},
          state_map: { new: "new" },
        },
      },
    })
    assert.ok(err.diagnostics.some((d) => d.message.includes("missing transform")))
  })

  it("rejects migration missing state mapping coverage", () => {
    const err = expectCompileFailure({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new", "open"],
          initial: "new",
          attributes: {},
          commands: { c: { emit: [{ type: "created", payload: {} }] } },
          reducers: { created: [] },
        },
      },
      migrations: {
        m0_to_1: {
          from: 0,
          to: 1,
          entity: "Ticket",
          event_transforms: { created: { emit_as: "created_v1" } },
          state_map: { new: "new" },
        },
      },
    })
    assert.ok(err.diagnostics.some((d) => d.message.includes("missing state mapping")))
  })

  it("rejects commands that emit events without reducers", () => {
    const err = expectCompileFailure({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          attributes: {},
          commands: { c: { emit: [{ type: "created", payload: {} }] } },
          reducers: {},
        },
      },
    })
    assert.ok(err.diagnostics.some((d) => d.message.includes("missing reducer")))
  })
})
