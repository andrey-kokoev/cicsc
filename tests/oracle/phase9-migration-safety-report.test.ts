import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 migration safety report", () => {
  it("publishes critical disposition with empty unresolved critical set", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-migration-safety-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-migration-safety-report-v1")
    assert.equal(report.status, "pass")
    assert.deepEqual(report.unresolved_criticals, [])
    for (const i of report.incident_disposition ?? []) {
      if (i.severity === "critical") {
        assert.ok(["closed", "deferred"].includes(i.status))
      }
      if (i.status === "deferred") {
        assert.equal(typeof i.owner, "string")
        assert.match(i.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
    }
  })
})
