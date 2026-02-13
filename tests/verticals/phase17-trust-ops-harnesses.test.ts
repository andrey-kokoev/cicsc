import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase17 trust/ops harnesses", () => {
  it("records pass status for trust/operations checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase17-trust-ops-harnesses.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase17-trust-ops-harnesses-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase17_baseline_status.status, "pass")
    assert.equal(r.checks.field_program_closure_status.status, "pass")
    assert.equal(r.checks.phase17_gate_status.status, "pass")
    assert.equal(r.checks.runbook_operator_contract.status, "pass")
  })
})
