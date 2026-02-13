import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase13 hardening matrix", () => {
  it("freezes hardening scope and evidence policy", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase13-hardening-matrix.json")
    const d = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(d.version, "cicsc/phase13-hardening-matrix-v1")
    assert.ok(Array.isArray(d.items))
    assert.ok(d.items.length >= 3)
    for (const i of d.items) {
      assert.equal(i.status, "in_scope")
      assert.equal(typeof i.evidence_target, "string")
    }
    assert.equal(d.policy.must_have_executable_evidence, true)
  })
})
