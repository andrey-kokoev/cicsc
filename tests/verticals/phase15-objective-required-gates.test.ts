import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase15 objective required gates", () => {
  it("records pass suite for required objective gates", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase15-objective-required-gates.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase15-objective-required-gates-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.category_model_conformance_status.status, "pass")
    assert.equal(r.checks.phase12_parity_envelope_status.status, "pass")
    assert.equal(r.checks.phase14_doc_consistency_status.status, "pass")
  })
})
