import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase19 runtime reliability matrix", () => {
  it("freezes runtime-reliability hardening scope and policy", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase19-runtime-reliability-matrix.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(r.version, "cicsc/phase19-runtime-reliability-matrix-v1")
    assert.equal(r.items.length, 3)
    assert.equal(r.policy.must_have_executable_evidence, true)
  })
})
