import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("policy DSL compilation", () => {
  it("compiles policy allow sugar into Core IR policy expressions", () => {
    const bundle = compileSpecToBundleV0({
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          commands: {},
          reducers: {},
        },
      },
      policies: {
        can_close: {
          params: ["actor"],
          allow: { role_is: "admin" },
        },
      },
    })

    const policy: any = bundle.core_ir.policies?.can_close
    assert.ok(policy)
    assert.deepEqual(policy.params, ["actor"])
    assert.equal(policy.expr.call.fn, "has_role")
  })
})
