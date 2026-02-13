import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 tenant-batch migration drill report", () => {
  it("records green batch migration drill and fault-injection checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-tenant-batch-migration-drill.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-tenant-batch-migration-drill-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.tenant_batch_drill.status, "pass")
    assert.equal(report.checks.migration_fault_injection.status, "pass")
  })
})
