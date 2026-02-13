import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"

describe("phase8 doc consistency gates", () => {
  it("passes status-drift check between PHASE8 and execution ledger", () => {
    const run = spawnSync("./scripts/check_phase8_docs_consistency.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)
  })
})
