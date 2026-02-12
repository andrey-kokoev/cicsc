import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { validateAuthIntrinsicsContract } from "../../core/vm/auth-contract"

describe("auth/role intrinsic contract", () => {
  it("accepts valid auth intrinsic surface", () => {
    const out = validateAuthIntrinsicsContract({
      has_role: () => true,
      role_of: () => "admin",
      auth_ok: () => true,
    } as any)
    assert.equal(out.ok, true)
  })

  it("rejects missing contract functions", () => {
    const out = validateAuthIntrinsicsContract({
      has_role: () => true,
    } as any)
    assert.equal(out.ok, false)
    if (out.ok) return
    assert.ok(out.errors.some((e) => e.path === "role_of"))
    assert.ok(out.errors.some((e) => e.path === "auth_ok"))
  })
})
