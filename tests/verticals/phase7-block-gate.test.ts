import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase7 block gate", () => {
  it("blocks Phase 7 unless phase6 exit checklist is fully pass", () => {
    const run = spawnSync("./scripts/check_phase7_block.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)

    const p = path.resolve(process.cwd(), "docs/pilot/phase7-gate.json")
    const gate = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(gate.version, "cicsc/phase7-gate-v1")
    assert.equal(gate.blocked, false)
    assert.deepEqual(gate.reasons, [])
  })
})
