import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase14 status register", () => {
  it("tracks phase14 items with status and owner/date accountability", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase14-status-register.json")
    const doc = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(doc.version, "cicsc/phase14-status-register-v1")
    assert.ok(Array.isArray(doc.items))
    assert.ok(doc.items.length >= 3)
    for (const i of doc.items) {
      assert.ok(["pending", "in_progress", "closed", "deferred"].includes(i.status))
      assert.equal(typeof i.owner, "string")
      assert.match(i.target_date, /^\d{4}-\d{2}-\d{2}$/)
      assert.equal(typeof i.basis, "string")
    }
  })
})
