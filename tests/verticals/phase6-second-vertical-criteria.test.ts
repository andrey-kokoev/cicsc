import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 second reference vertical criteria", () => {
  it("freezes crm as second reference vertical with objective criteria", () => {
    const p = path.resolve(process.cwd(), "verticals/crm/evaluation-criteria.phase6.json")
    const criteria = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(criteria.version, "cicsc/phase6-reference-vertical-v1")
    assert.equal(criteria.vertical, "crm")
    assert.ok(Array.isArray(criteria.acceptance_criteria))
    assert.ok(criteria.acceptance_criteria.length >= 5)
    assert.equal(criteria.artifacts.spec_v1, "verticals/crm/spec.v1.json")
  })
})
