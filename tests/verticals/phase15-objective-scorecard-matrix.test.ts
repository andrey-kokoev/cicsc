import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase15 objective scorecard matrix", () => {
  it("freezes objective evidence contract", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase15-objective-scorecard-matrix.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase15-objective-scorecard-matrix-v1")
    assert.equal(r.objectives.length, 5)
    for (const o of r.objectives ?? []) {
      assert.equal(typeof o.id, "string")
      assert.ok(Array.isArray(o.required_evidence))
      assert.ok(o.required_evidence.length >= 3)
    }
    assert.equal(r.evidence_contract.required_gates.length, 3)
  })
})
