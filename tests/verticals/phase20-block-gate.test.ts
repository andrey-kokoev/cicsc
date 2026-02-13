import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase20 block gate", () => {
  it("blocks unless phase19 checklist passes and AJ series is complete", () => {
    const checklist = JSON.parse(fs.readFileSync(path.resolve(process.cwd(), "docs/pilot/phase19-exit-checklist.json"), "utf8"))
    const checklistPass = (checklist.items ?? []).every((i: any) => i.status === "pass")
    const executionStatus = JSON.parse(
      fs.readFileSync(path.resolve(process.cwd(), "control-plane/views/execution-status.generated.json"), "utf8")
    )
    const rows = (executionStatus.rows ?? []).filter((r: any) => Number(r.phase_number) === 20)
    const allAj = rows.length > 0 && rows.every((r: any) => r.status === "done")
    const expectedBlocked = !(checklistPass && allAj)
    const run = spawnSync("./scripts/check_phase20_block.sh", { cwd: process.cwd(), encoding: "utf8" })
    const gate = JSON.parse(fs.readFileSync(path.resolve(process.cwd(), "docs/pilot/phase20-gate.json"), "utf8"))
    assert.equal(gate.version, "cicsc/phase20-gate-v1")
    assert.equal(gate.blocked, expectedBlocked)
    if (expectedBlocked) assert.notEqual(run.status, 0)
    else assert.equal(run.status, 0)
  })
})
