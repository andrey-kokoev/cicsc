import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase17 field-program matrix", () => {
  it("freezes field-program validation evidence contract", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase17-field-program-matrix.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase17-field-program-matrix-v1")
    assert.equal(r.tracks.length, 3)
    for (const t of r.tracks ?? []) {
      assert.equal(typeof t.id, "string")
      assert.ok(Array.isArray(t.required_evidence))
      assert.ok(t.required_evidence.length >= 3)
    }
    assert.equal(r.evidence_contract.required_gates.length, 3)
  })
})
