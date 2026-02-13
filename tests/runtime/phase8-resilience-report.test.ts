import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 resilience report", () => {
  it("publishes closed/deferred scenario disposition with no unresolved criticals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-resilience-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-resilience-report-v1")
    assert.deepEqual(report.unresolved_criticals, [])
    for (const i of report.incident_disposition ?? []) {
      if (i.severity === "critical" || i.severity === "high") {
        assert.ok(["closed", "deferred"].includes(i.status))
      }
    }
  })
})
