import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase18 block gate", () => {
  it("blocks unless phase17 checklist passes and AH series is complete", () => {
    const checklistPath = path.resolve(process.cwd(), "docs/pilot/phase17-exit-checklist.json")
    const checklist = JSON.parse(fs.readFileSync(checklistPath, "utf8"))
    const checklistPass = (checklist.items ?? []).every((i: any) => i.status === "pass")

    const roadmap = fs.readFileSync(path.resolve(process.cwd(), "ROADMAP.md"), "utf8")
    const ahMatches = [...roadmap.matchAll(/^- \[(x| )\] AH(\d)\.(\d)\s+/gm)]
    const allAhChecked = ahMatches.length > 0 && ahMatches.every((m) => m[1] === "x")
    const expectedBlocked = !(checklistPass && allAhChecked)

    const run = spawnSync("./scripts/check_phase18_block.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })

    const gatePath = path.resolve(process.cwd(), "docs/pilot/phase18-gate.json")
    const gate = JSON.parse(fs.readFileSync(gatePath, "utf8"))
    assert.equal(gate.version, "cicsc/phase18-gate-v1")
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
