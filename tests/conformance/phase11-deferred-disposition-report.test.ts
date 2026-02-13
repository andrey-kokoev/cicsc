import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 deferred disposition report", () => {
  it("publishes explicit closure/defer disposition with no unresolved criticals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-deferred-disposition-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase11-deferred-disposition-report-v1")
    assert.equal(report.status, "pass")
    assert.deepEqual(report.unresolved_criticals, [])
    assert.ok(report.items.some((i: any) => i.status === "closed"))
    for (const i of report.items) {
      if (i.status === "deferred") {
        assert.equal(typeof i.owner, "string")
        assert.match(i.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
    }
  })
})
