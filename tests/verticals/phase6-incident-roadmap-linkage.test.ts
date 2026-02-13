import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"
import { spawnSync } from "node:child_process"


function loadExecutionStatus() {
  const run = spawnSync("./control-plane/scripts/export_execution_status.py", ["control-plane/execution/execution-ledger.yaml"], {
    cwd: process.cwd(),
    encoding: "utf8",
  })
  assert.equal(run.status, 0, run.stderr || run.stdout)
  return JSON.parse(run.stdout)
}

describe("phase6 comparative incident -> execution-structure linkage", () => {
  it("maps each comparative incident id into explicit execution-structure entries", () => {
    const incidentPath = path.resolve(process.cwd(), "docs/pilot/phase6-comparative-incidents.json")
    const mapPath = path.resolve(process.cwd(), "docs/pilot/phase6-findings-roadmap-map.md")
        const incidents = JSON.parse(fs.readFileSync(incidentPath, "utf8"))
    const mapDoc = fs.readFileSync(mapPath, "utf8")
    const executionStatus = loadExecutionStatus()
    const checkboxIds = new Set((executionStatus.rows ?? []).map((r: any) => String(r.checkbox_id)))
    const mapping = new Map<string, string>()
    for (const m of mapDoc.matchAll(/- `([^`]+)` -> `([^`]+)`/g)) {
      mapping.set(String(m[1]), String(m[2]))
    }

    for (const incident of incidents.incidents ?? []) {
      const cid = mapping.get(String(incident.id))
      assert.ok(cid, `missing mapping row for ${incident.id}`)
      assert.equal(checkboxIds.has(String(cid)), true, `mapped checkbox missing in execution status for ${incident.id}`)
    }
  })
})
