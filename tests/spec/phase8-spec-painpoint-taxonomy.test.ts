import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 spec pain-point taxonomy", () => {
  it("freezes field-derived taxonomy categories with recommendations", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-spec-painpoint-taxonomy.json")
    const t = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(t.version, "cicsc/phase8-spec-painpoint-taxonomy-v1")
    assert.ok(Array.isArray(t.categories))
    assert.equal(t.categories.length >= 3, true)
    for (const c of t.categories) {
      assert.equal(typeof c.id, "string")
      assert.equal(typeof c.recommendation, "string")
    }
  })
})
