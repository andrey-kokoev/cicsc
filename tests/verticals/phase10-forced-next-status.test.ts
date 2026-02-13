import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 forced-next status", () => {
  it("records owner/date discipline for deferred forced-next items", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase10-forced-next-status.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(report.version, "cicsc/phase10-forced-next-status-v1")
    assert.ok(Array.isArray(report.items))
    for (const i of report.items) {
      assert.equal(typeof i.owner, "string")
      if (i.status === "deferred") {
        assert.match(i.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
      assert.ok(["closed", "deferred"].includes(i.status))
    }
  })
})
