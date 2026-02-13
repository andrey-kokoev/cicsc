import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase5 incident -> execution-structure linkage", () => {
  it("maps each incident id into explicit execution-structure backlog items", () => {
    const incidentPath = path.resolve(process.cwd(), "docs/pilot/phase5-ticketing-incidents.json")
    const mapPath = path.resolve(process.cwd(), "docs/pilot/phase5-findings-roadmap-map.md")
    const executionStatusPath = path.resolve(process.cwd(), "control-plane/views/execution-status.generated.json")
    const incidents = JSON.parse(fs.readFileSync(incidentPath, "utf8"))
    const mapDoc = fs.readFileSync(mapPath, "utf8")
    const executionStatus = JSON.parse(fs.readFileSync(executionStatusPath, "utf8"))
    const checkboxIds = new Set((executionStatus.rows ?? []).map((r: any) => String(r.checkbox_id)))
    const mapping = new Map<string, string>()
    for (const m of mapDoc.matchAll(/- `([^`]+)` -> `([^`]+)`/g)) {
      mapping.set(String(m[1]), String(m[2]))
    }

    for (const incident of incidents.incidents ?? []) {
      const cid = mapping.get(String(incident.id))
      assert.ok(cid, `missing mapping row for ${incident.id}`)
      if (/^[A-Z]{1,2}\d+\.\d+$/.test(String(cid))) {
        assert.equal(checkboxIds.has(String(cid)), true, `mapped checkbox missing in execution status for ${incident.id}`)
      }
    }
  })
})
