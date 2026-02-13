import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 operational slo continuity gate", () => {
  it("records green operational continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase10-operational-slo-continuity.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(report.version, "cicsc/phase10-operational-slo-continuity-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.phase9_resilience_slo.status, "pass")
    assert.equal(report.checks.phase10_parity_continuity.status, "pass")
    assert.equal(report.checks.phase10_migration_continuity.status, "pass")
  })
})
