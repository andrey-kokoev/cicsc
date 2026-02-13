import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 comparative incident -> roadmap linkage", () => {
  it("maps each comparative incident id into explicit roadmap entries", () => {
    const incidentPath = path.resolve(process.cwd(), "docs/pilot/phase6-comparative-incidents.json")
    const roadmapPath = path.resolve(process.cwd(), "ROADMAP.md")
    const incidents = JSON.parse(fs.readFileSync(incidentPath, "utf8"))
    const roadmap = fs.readFileSync(roadmapPath, "utf8")

    for (const incident of incidents.incidents ?? []) {
      assert.equal(roadmap.includes(String(incident.id)), true, `missing roadmap mapping for ${incident.id}`)
    }
  })
})
