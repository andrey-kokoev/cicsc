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

describe("phase7 parity delta -> execution-structure linkage", () => {
  it("maps each parity delta id into explicit execution-structure entries", () => {
    const deltaPath = path.resolve(process.cwd(), "docs/pilot/phase7-parity-deltas.json")
        const deltas = JSON.parse(fs.readFileSync(deltaPath, "utf8"))
    const executionStatus = loadExecutionStatus()
    const checkboxIds = new Set((executionStatus.rows ?? []).map((r: any) => String(r.checkbox_id)))

    for (const d of deltas.deltas ?? []) {
      assert.ok(d.mapped_roadmap_item, `missing mapped checkbox id for ${d.id}`)
      assert.equal(checkboxIds.has(String(d.mapped_roadmap_item)), true, `missing execution-status mapping for ${d.id}`)
    }
  })
})
