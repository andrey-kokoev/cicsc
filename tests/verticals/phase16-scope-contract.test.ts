import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase16 scope contract", () => {
  it("defines phase16 tracks with owner/date accountability", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase16-scope-contract.json")
    const doc = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(doc.version, "cicsc/phase16-scope-contract-v1")
    assert.equal(doc.phase, "phase16")
    assert.ok(Array.isArray(doc.tracks))
    assert.ok(doc.tracks.length >= 3)
    for (const t of doc.tracks) {
      assert.equal(typeof t.id, "string")
      assert.equal(typeof t.owner, "string")
      assert.match(t.target_date, /^\d{4}-\d{2}-\d{2}$/)
    }
  })
})
