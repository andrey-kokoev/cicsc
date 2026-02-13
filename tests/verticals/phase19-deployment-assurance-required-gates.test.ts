import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase19 deployment-assurance required gates", () => {
  it("records pass suite for required deployment-assurance gates", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase19-deployment-assurance-required-gates.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(r.version, "cicsc/phase19-deployment-assurance-required-gates-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase18_doc_consistency_status.status, "pass")
    assert.equal(r.checks.phase18_expansion_proof_required_gates_status.status, "pass")
    assert.equal(r.checks.phase19_baseline_continuity_status.status, "pass")
  })
})
