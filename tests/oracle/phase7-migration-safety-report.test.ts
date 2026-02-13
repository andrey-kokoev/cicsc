import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 migration safety report", () => {
  it("publishes critical disposition closure with no unresolved criticals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-migration-safety-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-migration-safety-report-v1")
    assert.deepEqual(report.unresolved_criticals, [])
    for (const i of report.incident_disposition ?? []) {
      if (i.severity === "critical" || i.severity === "high") {
        assert.ok(["closed", "deferred"].includes(i.status))
      }
    }
  })
})
