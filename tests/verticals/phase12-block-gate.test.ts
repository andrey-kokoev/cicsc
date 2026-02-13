import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"
import { spawnSync } from "node:child_process"

describe("phase12 block gate", () => {
  it("blocks/unblocks based on phase11 exit checklist truth", () => {
    const checklistPath = path.resolve(process.cwd(), "docs/pilot/phase11-exit-checklist.json")
    const checklist = JSON.parse(fs.readFileSync(checklistPath, "utf8"))
    const allPass = (checklist.items ?? []).every((i: any) => i.status === "pass")

    const run = spawnSync("./scripts/check_phase12_block.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })

    const gatePath = path.resolve(process.cwd(), "docs/pilot/phase12-gate.json")
    const gate = JSON.parse(fs.readFileSync(gatePath, "utf8"))

    assert.equal(gate.version, "cicsc/phase12-gate-v1")
    assert.equal(gate.blocked, !allPass)
    if (allPass) {
      assert.equal(run.status, 0, run.stderr || run.stdout)
      assert.deepEqual(gate.reasons, [])
    } else {
      assert.notEqual(run.status, 0)
      assert.ok(Array.isArray(gate.reasons))
      assert.ok(gate.reasons.length >= 1)
    }
  })
})
