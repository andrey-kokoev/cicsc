import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase16 external-validation required gates", () => {
  it("records pass suite for required external-validation gates", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase16-external-validation-required-gates.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase16-external-validation-required-gates-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase15_doc_consistency_status.status, "pass")
    assert.equal(r.checks.phase15_objective_required_gates_status.status, "pass")
    assert.equal(r.checks.phase16_baseline_continuity_status.status, "pass")
  })
})
