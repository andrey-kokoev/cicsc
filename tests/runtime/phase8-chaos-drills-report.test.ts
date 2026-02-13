import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 chaos drills report", () => {
  it("records green outage/verify-delay/backpressure checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-chaos-drills.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-chaos-drills-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.chaos_drill_models.status, "pass")
    assert.equal(report.checks.tenant_batch_migration.status, "pass")
    assert.equal(report.checks.verify_streaming.status, "pass")
  })
})
