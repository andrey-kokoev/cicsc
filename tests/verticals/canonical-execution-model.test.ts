import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"

describe("canonical execution model", () => {
  it("passes through canonical gate entrypoint", () => {
    const run = spawnSync("./control-plane/check_gates.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)
  })
})
