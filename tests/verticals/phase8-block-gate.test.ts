import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase8 block gate", () => {
  it("blocks Phase 8 unless phase7 exit checklist is fully pass", () => {
    const run = spawnSync("./scripts/check_phase8_block.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)

    const p = path.resolve(process.cwd(), "docs/pilot/phase8-gate.json")
    const gate = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(gate.version, "cicsc/phase8-gate-v1")
    assert.equal(gate.blocked, false)
    assert.deepEqual(gate.reasons, [])
  })
})
