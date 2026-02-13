import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase5 reference vertical criteria", () => {
  it("freezes ticketing as reference vertical with objective acceptance criteria", () => {
    const p = path.resolve(process.cwd(), "verticals/ticketing/evaluation-criteria.phase5.json")
    const criteria = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(criteria.version, "cicsc/phase5-reference-vertical-v1")
    assert.equal(criteria.vertical, "ticketing")
    assert.ok(Array.isArray(criteria.acceptance_criteria))
    assert.ok(criteria.acceptance_criteria.length >= 5)
    assert.equal(criteria.artifacts.spec_v1, "verticals/ticketing/spec.v1.json")
  })
})
