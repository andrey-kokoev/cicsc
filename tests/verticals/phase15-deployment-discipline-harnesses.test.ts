import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase15 deployment-discipline harnesses", () => {
  it("records pass status for deployment discipline checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase15-deployment-discipline-harnesses.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase15-deployment-discipline-harnesses-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.runbook_operator_contract.status, "pass")
    assert.equal(r.checks.phase15_baseline_status.status, "pass")
    assert.equal(r.checks.objective_required_gates_status.status, "pass")
    assert.equal(r.checks.phase15_gate_status.status, "pass")
  })
})
