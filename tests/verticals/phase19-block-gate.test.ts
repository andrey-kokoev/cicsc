import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"


function loadExecutionStatus() {
  const run = spawnSync("./control-plane/scripts/export_execution_status.py", ["control-plane/execution/execution-ledger.yaml"], {
    cwd: process.cwd(),
    encoding: "utf8",
  })
  assert.equal(run.status, 0, run.stderr || run.stdout)
  return JSON.parse(run.stdout)
}

describe("phase19 block gate", () => {
  it("blocks unless phase18 checklist passes and AI series is complete", () => {
    const checklistPath = path.resolve(process.cwd(), "docs/pilot/phase18-exit-checklist.json")
    const checklist = JSON.parse(fs.readFileSync(checklistPath, "utf8"))
    const checklistPass = (checklist.items ?? []).every((i: any) => i.status === "pass")

    const executionStatus = loadExecutionStatus()
    const rows = (executionStatus.rows ?? []).filter((r: any) => Number(r.phase_number) === 19)
    const allAiChecked = rows.length > 0 && rows.every((r: any) => r.status === "done")
    const expectedBlocked = !(checklistPass && allAiChecked)

    const run = spawnSync("./scripts/check_phase19_block.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })

    const gatePath = path.resolve(process.cwd(), "docs/pilot/phase19-gate.json")
    const gate = JSON.parse(fs.readFileSync(gatePath, "utf8"))
    assert.equal(gate.version, "cicsc/phase19-gate-v1")
    assert.equal(gate.blocked, expectedBlocked)

    if (expectedBlocked) {
      assert.notEqual(run.status, 0)
      assert.ok(Array.isArray(gate.reasons))
      assert.ok(gate.reasons.length >= 1)
    } else {
      assert.equal(run.status, 0, run.stderr || run.stdout)
      assert.deepEqual(gate.reasons, [])
    }
  })
})
