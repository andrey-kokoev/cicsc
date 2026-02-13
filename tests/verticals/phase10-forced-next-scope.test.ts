import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 forced-next scope", () => {
  it("freezes forced-next tracks with explicit owners", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase10-forced-next-scope.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(report.version, "cicsc/phase10-forced-next-scope-v1")
    assert.ok(Array.isArray(report.tracks))
    assert.equal(report.tracks.length, 3)
    for (const t of report.tracks) {
      assert.equal(t.status, "in_scope")
      assert.equal(typeof t.owner, "string")
      assert.ok(t.owner.length > 0)
    }
  })
})
