import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 baseline gates", () => {
  it("records pass baseline across parity/migration/ops/governance", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-baseline-gates.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase11-baseline-gates-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.parity_continuity.status, "pass")
    assert.equal(report.checks.migration_continuity.status, "pass")
    assert.equal(report.checks.operational_slo_continuity.status, "pass")
    assert.equal(report.checks.governance_drift_gate.status, "pass")
    assert.equal(report.checks.phase11_block_gate.status, "pass")
  })
})
