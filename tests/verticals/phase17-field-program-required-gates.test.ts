import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase17 field-program required gates", () => {
  it("records pass suite for required field-program gates", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase17-field-program-required-gates.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase17-field-program-required-gates-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase16_doc_consistency_status.status, "pass")
    assert.equal(r.checks.phase16_external_validation_required_gates_status.status, "pass")
    assert.equal(r.checks.phase17_baseline_continuity_status.status, "pass")
  })
})
