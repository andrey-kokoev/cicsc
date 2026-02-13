import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"

describe("canonical execution model", () => {
  it("passes execution-ledger integrity, phase-view sync, and commit evidence checks", () => {
    const run = spawnSync("./scripts/check_canonical_execution_model.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)
  })
})
