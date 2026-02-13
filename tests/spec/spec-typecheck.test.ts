import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"
import { CompileDiagnosticsError } from "../../runtime/http/compile"
import { parseSpecV0 } from "../../spec/parse-yaml"
import { typecheckSpecV0 } from "../../spec/typecheck"

describe("spec typechecking", () => {
  it("rejects invalid initial state at spec layer", () => {
    const spec = parseSpecV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "done",
          attributes: {},
          commands: { c: { emit: [{ type: "created", payload: {} }] } },
          reducers: { created: [] },
        },
      },
    })
    const stc = typecheckSpecV0(spec)
    assert.equal(stc.ok, false)
    if (stc.ok) return
    assert.ok(stc.errors.some((e) => e.path === "entities.Ticket.initial"))
  })

  it("fails compile before IR typecheck when emitted reducer is missing", () => {
    assert.throws(
      () =>
        compileSpecToBundleV0({
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
        }),
      /spec typecheck failed/
    )
  })

  it("emits path-qualified diagnostics for rejected spec constructs", () => {
    try {
      compileSpecToBundleV0({
        version: 0,
        entities: {
          Ticket: {
            id: "string",
            states: ["new"],
            initial: "done",
            attributes: {},
            commands: { c: { emit: [{ type: "created", payload: {} }] } },
            reducers: {},
          },
        },
      })
      assert.fail("expected CompileDiagnosticsError")
    } catch (e: any) {
      assert.ok(e instanceof CompileDiagnosticsError)
      assert.equal(Array.isArray(e.diagnostics), true)
      assert.ok(e.diagnostics.some((d: any) => d.path === "entities.Ticket.initial"))
      assert.ok(e.diagnostics.every((d: any) => typeof d.path === "string" && d.path.length > 0))
    }
  })
})
