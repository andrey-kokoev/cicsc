import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 migration drills", () => {
  it("records green migration drill suites", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-migration-drills.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-migration-drills-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.tenant_batch_migration.status, "pass")
    assert.equal(report.checks.migration_authoring_assistant.status, "pass")
    assert.equal(report.checks.migration_protocol_check.status, "pass")
  })
})
