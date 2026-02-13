import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase19 deployment-assurance matrix", () => {
  it("freezes deployment-assurance evidence contract", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase19-deployment-assurance-matrix.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(r.version, "cicsc/phase19-deployment-assurance-matrix-v1")
    assert.equal(r.tracks.length, 3)
    assert.equal(r.evidence_contract.required_gates.length, 3)
  })
})
