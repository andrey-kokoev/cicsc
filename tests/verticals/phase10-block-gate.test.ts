import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase10 block gate", () => {
  it("blocks Phase 10 unless phase9 exit checklist is fully pass", () => {
    const run = spawnSync("./scripts/check_phase10_block.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)

    const p = path.resolve(process.cwd(), "docs/pilot/phase10-gate.json")
    const gate = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(gate.version, "cicsc/phase10-gate-v1")
    assert.equal(gate.blocked, false)
    assert.deepEqual(gate.reasons, [])
  })
})
