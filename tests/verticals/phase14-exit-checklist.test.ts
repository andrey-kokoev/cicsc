import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase14 exit checklist", () => {
  it("maps all exit items to artifacts with pass status", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase14-exit-checklist.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase14-exit-checklist-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.items.length, 4)
    for (const item of r.items ?? []) {
      assert.equal(item.status, "pass")
      assert.equal(typeof item.artifact, "string")
      assert.ok(item.artifact.startsWith("docs/pilot/"))
    }
  })
})
