import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { CompileDiagnosticsError, compileSpecToBundleV0 } from "../../runtime/http/compile"

function ticketSpec () {
  return {
    version: 0,
    entities: {
      Ticket: {
        id: "string",
        states: ["new"],
        initial: "new",
        commands: {
          Create: { emit: [{ type: "Created", payload: {} }] },
        },
        reducers: {
          Created: [{ set_state: "new" }],
        },
      },
    },
  }
}

describe("intent-plane compile preflight", () => {
  it("rejects non-deployable intent-plane envelope before compile", () => {
    assert.throws(
      () =>
        compileSpecToBundleV0({
          spec: ticketSpec(),
          deployable: false,
          blocking_issues: ["Entity Ticket has no commands."],
        }),
      (err: unknown) => {
        assert.ok(err instanceof CompileDiagnosticsError)
        assert.match(String((err as Error).message), /preflight failed/i)
        assert.equal((err as CompileDiagnosticsError).diagnostics[0]?.path, "$.blocking_issues[0]")
        return true
      }
    )
  })

  it("accepts deployable intent-plane envelope", () => {
    const bundle = compileSpecToBundleV0({
      spec: ticketSpec(),
      deployable: true,
      blocking_issues: [],
    })
    assert.equal(bundle.core_ir.version, 0)
  })
})
