import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 migration concurrency drill report", () => {
  it("records green pause/migrate/resume checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-migration-concurrency-drill.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase6-migration-concurrency-drill-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.migration_pause_resume.status, "pass")
    assert.equal(report.checks.migration_protocol_core.status, "pass")
  })
})
