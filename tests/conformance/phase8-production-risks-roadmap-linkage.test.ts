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

describe("phase8 production risk -> execution-structure linkage", () => {
  it("maps each exclusion/risk id into execution-structure text", () => {
    const reportPath = path.resolve(process.cwd(), "docs/pilot/phase8-production-equivalence-report.json")
    const mapPath = path.resolve(process.cwd(), "docs/pilot/phase8-production-risks-roadmap-map.md")
        const report = JSON.parse(fs.readFileSync(reportPath, "utf8"))
    const mapDoc = fs.readFileSync(mapPath, "utf8")
    const executionStatus = loadExecutionStatus()
    const checkboxIds = new Set((executionStatus.rows ?? []).map((r: any) => String(r.checkbox_id)))
    const mapping = new Map<string, string>()
    for (const m of mapDoc.matchAll(/- `([^`]+)` -> `([^`]+)`/g)) {
      mapping.set(String(m[1]), String(m[2]))
    }

    for (const r of report.risk_labels ?? []) {
      const cid = mapping.get(String(r.id))
      assert.ok(cid, `missing mapping row for ${r.id}`)
      assert.equal(checkboxIds.has(String(cid)), true, `mapped checkbox missing in execution status for ${r.id}`)
    }
    for (const e of report.exclusions ?? []) {
      const cid = mapping.get(String(e.id))
      assert.ok(cid, `missing mapping row for ${e.id}`)
      assert.equal(checkboxIds.has(String(cid)), true, `mapped checkbox missing in execution status for ${e.id}`)
    }
  })
})
