import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 parity triage", () => {
  it("publishes regression classes with owner + disposition", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-parity-triage.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-parity-triage-v1")
    const classes = report.regression_classes ?? []
    assert.ok(classes.length >= 3)

    for (const c of classes) {
      assert.equal(typeof c.id, "string")
      assert.equal(typeof c.owner, "string")
      assert.ok(["closed", "deferred"].includes(c.status))
      if (c.status === "deferred") {
        assert.match(c.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
    }
  })
})
