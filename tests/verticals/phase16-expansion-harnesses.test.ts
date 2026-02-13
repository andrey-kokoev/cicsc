import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase16 expansion harnesses", () => {
  it("records pass status for expansion-readiness checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase16-expansion-harnesses.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase16-expansion-harnesses-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase16_baseline_status.status, "pass")
    assert.equal(r.checks.external_validation_status.status, "pass")
    assert.equal(r.checks.phase16_gate_status.status, "pass")
    assert.equal(r.checks.runbook_operator_contract.status, "pass")
  })
})
