import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("per-command auth mapping", () => {
  it("injects auth_ok guard when command auth is declared", () => {
    const bundle = compileSpecToBundleV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          commands: {
            close: {
              when: { state_is: "new" },
              auth: { policy: "can_close" },
              emit: [{ type: "closed", payload: {} }],
            },
          },
          reducers: {
            closed: [{ set_state: "new" }],
          },
        },
      },
    })

    const guard: any = (bundle.core_ir.types as any).Ticket.commands.close.guard.expr
    assert.ok(Array.isArray(guard.and))
    const auth = guard.and.find((x: any) => x?.call?.fn === "auth_ok")
    assert.ok(auth)
    assert.equal(auth.call.args[1].lit.string, "can_close")
  })
})
