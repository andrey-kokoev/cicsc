import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 production risk -> roadmap linkage", () => {
  it("maps each exclusion/risk id into roadmap text", () => {
    const reportPath = path.resolve(process.cwd(), "docs/pilot/phase8-production-equivalence-report.json")
    const roadmapPath = path.resolve(process.cwd(), "ROADMAP.md")
    const report = JSON.parse(fs.readFileSync(reportPath, "utf8"))
    const roadmap = fs.readFileSync(roadmapPath, "utf8")

    for (const r of report.risk_labels ?? []) {
      assert.equal(roadmap.includes(String(r.id)), true, `missing roadmap mapping for ${r.id}`)
    }
    for (const e of report.exclusions ?? []) {
      assert.equal(roadmap.includes(String(e.id)), true, `missing roadmap mapping for ${e.id}`)
    }
  })
})
