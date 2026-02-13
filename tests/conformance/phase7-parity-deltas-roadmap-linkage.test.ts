import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 parity delta -> roadmap linkage", () => {
  it("maps each parity delta id into explicit roadmap entries", () => {
    const deltaPath = path.resolve(process.cwd(), "docs/pilot/phase7-parity-deltas.json")
    const roadmapPath = path.resolve(process.cwd(), "ROADMAP.md")
    const deltas = JSON.parse(fs.readFileSync(deltaPath, "utf8"))
    const roadmap = fs.readFileSync(roadmapPath, "utf8")

    for (const d of deltas.deltas ?? []) {
      assert.equal(roadmap.includes(String(d.id)), true, `missing roadmap mapping for ${d.id}`)
    }
  })
})
