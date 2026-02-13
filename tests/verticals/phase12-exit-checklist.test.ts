import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase12 exit checklist", () => {
  it("is objective and mapped to concrete artifacts", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase12-exit-checklist.json")
    const checklist = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(checklist.version, "cicsc/phase12-exit-checklist-v1")
    assert.ok(Array.isArray(checklist.items))
    assert.ok(checklist.items.length >= 5)
    for (const item of checklist.items) {
      assert.ok(Array.isArray(item.artifacts))
      assert.ok(item.artifacts.length >= 1)
      assert.ok(["pass", "pending", "fail"].includes(item.status))
    }
  })
})
