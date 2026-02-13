import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 multi-vertical field report", () => {
  it("ensures unresolved criticals are closed or explicitly deferred", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-multi-vertical-field-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase6-multi-vertical-field-report-v1")
    assert.deepEqual(report.unresolved_criticals, [])

    for (const i of report.incident_disposition ?? []) {
      if (i.severity === "critical" || i.severity === "high") {
        assert.ok(["closed", "deferred"].includes(i.status))
      }
    }
  })
})
