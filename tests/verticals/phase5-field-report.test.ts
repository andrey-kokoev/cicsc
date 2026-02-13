import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase5 field report", () => {
  it("publishes forced-next priorities only", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase5-ticketing-field-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase5-field-report-v1")
    assert.equal(report.vertical, "ticketing")
    assert.ok(Array.isArray(report.forced_next_priorities))
    assert.deepEqual(
      report.forced_next_priorities.map((x: any) => x.roadmap_id),
      []
    )
  })
})
