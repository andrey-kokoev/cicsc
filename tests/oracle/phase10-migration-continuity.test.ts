import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 migration continuity gate", () => {
  it("records green migration continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase10-migration-continuity.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(report.version, "cicsc/phase10-migration-continuity-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.phase9_migration_drills.status, "pass")
    assert.equal(report.checks.phase9_post_cutover_diff.status, "pass")
    assert.equal(report.checks.phase9_migration_safety_report.status, "pass")
  })
})
