import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase14 readiness harnesses", () => {
  it("records pass status for runbook, slo, and diagnostics checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase14-readiness-harnesses.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase14-readiness-harnesses-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.runbook_contract.status, "pass")
    assert.equal(r.checks.slo_gate_status.status, "pass")
    assert.equal(r.checks.diagnostics_gate_status.status, "pass")
  })
})
