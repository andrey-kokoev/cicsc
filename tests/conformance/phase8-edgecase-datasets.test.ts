import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 edgecase dataset contract", () => {
  it("defines null/collation/numeric edge datasets", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-edgecase-datasets.json")
    const d = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(d.version, "cicsc/phase8-edgecase-datasets-v1")
    assert.ok(Array.isArray(d.datasets.null_cases))
    assert.ok(Array.isArray(d.datasets.collation_cases))
    assert.ok(Array.isArray(d.datasets.numeric_cases))
    assert.equal(d.datasets.null_cases.length >= 1, true)
    assert.equal(d.datasets.collation_cases.length >= 1, true)
    assert.equal(d.datasets.numeric_cases.length >= 1, true)
  })
})
