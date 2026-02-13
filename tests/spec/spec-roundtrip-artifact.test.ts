import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"

import { validateBundleV0 } from "../../core/ir/validate"
import { verifyHistoryAgainstIr } from "../../core/runtime/verify"
import { compileSpecToBundleV0 } from "../../runtime/http/compile"
import type { VmIntrinsics } from "../../core/vm/eval"

const intrinsics: VmIntrinsics = {
  has_role: () => false,
  role_of: () => "user",
  auth_ok: () => true,
  constraint: () => true,
  len: (v) => (Array.isArray(v) || typeof v === "string" ? v.length : null),
  str: (v) => (v == null ? null : String(v)),
  int: (v) => (typeof v === "number" ? Math.trunc(v) : null),
  float: (v) => (typeof v === "number" ? v : null),
}

describe("spec roundtrip artifact contract", () => {
  it("matches frozen spec->bundle->verify artifact", () => {
    const spec = JSON.parse(readFileSync("spec/contracts/spec-dsl-v1.fixture.json", "utf8"))
    const expected = JSON.parse(readFileSync("spec/contracts/spec-dsl-v1.roundtrip.json", "utf8"))

    const bundle = compileSpecToBundleV0(spec)
    const valid = validateBundleV0(bundle)
    const verify = verifyHistoryAgainstIr({
      bundle,
      events: [],
      now: 0,
      actor: "roundtrip",
      intrinsics,
    })

    const actual = {
      version: "cicsc/spec-roundtrip-v1",
      bundle_valid: valid.ok,
      types_count: Object.keys(bundle.core_ir.types ?? {}).length,
      views_count: Object.keys(bundle.core_ir.views ?? {}).length,
      migrations_count: Object.keys(bundle.core_ir.migrations ?? {}).length,
      verify_ok: verify.ok,
    }

    assert.deepEqual(actual, expected)
  })
})
