import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase5 exit checklist", () => {
  it("defines objective artifact-mapped criteria and readiness flag", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase5-exit-checklist.json")
    const checklist = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(checklist.version, "cicsc/phase5-exit-checklist-v1")
    assert.ok(Array.isArray(checklist.items))
    assert.ok(checklist.items.length >= 5)
    for (const item of checklist.items) {
      assert.ok(item.id)
      assert.ok(item.criterion)
      assert.ok(item.artifact)
      assert.ok(["pass", "blocked", "fail", "pending"].includes(item.status))
    }
    assert.equal(typeof checklist.phase6_ready, "boolean")
  })
})
