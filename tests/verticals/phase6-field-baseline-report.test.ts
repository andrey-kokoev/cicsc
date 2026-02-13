import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 field baseline report", () => {
  it("publishes only forced-next priorities from comparative incidents", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-field-baseline-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase6-field-baseline-report-v1")
    assert.deepEqual(report.verticals, ["ticketing", "crm"])
    assert.equal(report.status.overall, "pass")
    assert.equal(report.status.cross_vertical_gaps_explicit, true)

    assert.deepEqual(
      report.forced_next_priorities.map((x: any) => x.roadmap_id),
      ["W4.2", "W3.5", "W2.4"]
    )
  })
})
