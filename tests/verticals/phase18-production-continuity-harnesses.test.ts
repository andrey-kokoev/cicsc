import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase18 production-continuity harnesses", () => {
  it("records pass status for production-continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase18-production-continuity-harnesses.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase18-production-continuity-harnesses-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase18_baseline_status.status, "pass")
    assert.equal(r.checks.expansion_proof_closure_status.status, "pass")
    assert.equal(r.checks.phase18_gate_status.status, "pass")
    assert.equal(r.checks.runbook_operator_contract.status, "pass")
  })
})
