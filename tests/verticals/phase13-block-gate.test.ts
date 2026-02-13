import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase13 block gate", () => {
  it("matches phase12 exit checklist pass/fail truth", () => {
    const checklistPath = path.resolve(process.cwd(), "docs/pilot/phase12-exit-checklist.json")
    const checklist = JSON.parse(fs.readFileSync(checklistPath, "utf8"))
    const allPass = (checklist.items ?? []).every((i: any) => i.status === "pass")

    const run = spawnSync("./scripts/check_phase13_block.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })

    const gatePath = path.resolve(process.cwd(), "docs/pilot/phase13-gate.json")
    const gate = JSON.parse(fs.readFileSync(gatePath, "utf8"))
    assert.equal(gate.version, "cicsc/phase13-gate-v1")
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
