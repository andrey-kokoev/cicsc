import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase12 parity envelope matrix", () => {
  it("freezes in-scope envelope items and parity policy", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase12-parity-envelope-matrix.json")
    const doc = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(doc.version, "cicsc/phase12-parity-envelope-matrix-v1")
    assert.ok(Array.isArray(doc.envelope_items))
    assert.ok(doc.envelope_items.length >= 3)
    for (const i of doc.envelope_items) {
      assert.equal(i.status, "in_scope")
      assert.equal(typeof i.evidence_target, "string")
    }
    assert.equal(doc.policy.must_have_differential_evidence, true)
    assert.equal(doc.policy.unsupported_surface_requires_compile_time_reject, true)
  })
})
