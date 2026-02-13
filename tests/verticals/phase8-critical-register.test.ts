import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 critical register", () => {
  it("has no unresolved criticals and owner-dated deferrals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-critical-register.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-critical-register-v1")
    assert.equal(report.status, "pass")
    assert.deepEqual(report.open_critical_items, [])

    for (const d of report.deferred_items ?? []) {
      assert.equal(d.status, "deferred")
      assert.equal(typeof d.owner, "string")
      assert.ok(d.owner.length > 0)
      assert.match(d.target_date, /^\d{4}-\d{2}-\d{2}$/)
    }
  })
})
