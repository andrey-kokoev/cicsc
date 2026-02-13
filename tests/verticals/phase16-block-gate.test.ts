import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase16 block gate", () => {
  it("blocks unless phase15 checklist passes and AF series is complete", () => {
    const checklistPath = path.resolve(process.cwd(), "docs/pilot/phase15-exit-checklist.json")
    const checklist = JSON.parse(fs.readFileSync(checklistPath, "utf8"))
    const checklistPass = (checklist.items ?? []).every((i: any) => i.status === "pass")

    const executionStatus = JSON.parse(
      fs.readFileSync(path.resolve(process.cwd(), "control-plane/views/execution-status.generated.json"), "utf8")
    )
    const rows = (executionStatus.rows ?? []).filter((r: any) => Number(r.phase_number) === 16)
    const allAfChecked = rows.length > 0 && rows.every((r: any) => r.status === "done")
    const expectedBlocked = !(checklistPass && allAfChecked)

    const run = spawnSync("./scripts/check_phase16_block.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })

    const gatePath = path.resolve(process.cwd(), "docs/pilot/phase16-gate.json")
    const gate = JSON.parse(fs.readFileSync(gatePath, "utf8"))
    assert.equal(gate.version, "cicsc/phase16-gate-v1")
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
