import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase19 exit checklist", () => {
  it("maps all exit items to artifacts with pass status", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase19-exit-checklist.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(r.version, "cicsc/phase19-exit-checklist-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.items.length, 4)
  })
})
