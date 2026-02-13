import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"

describe("commit subject policy", () => {
  it("passes for recent repository history", () => {
    const run = spawnSync("./scripts/check_commit_subjects.sh", ["HEAD~30", "HEAD"], {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)
  })
})
