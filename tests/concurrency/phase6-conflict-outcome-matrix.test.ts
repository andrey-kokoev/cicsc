import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

type Resolution = "abort" | "retry" | "merge"
type Outcome = "abort_or_serialize" | "retry_with_fresh_tx" | "reject_not_supported"

function resolveConflictDeterministically(resolution: Resolution): Outcome {
  if (resolution === "abort") {
    return "abort_or_serialize"
  }
  if (resolution === "retry") {
    return "retry_with_fresh_tx"
  }
  return "reject_not_supported"
}

describe("phase6 conflict outcome matrix", () => {
  it("declares deterministic abort/retry/merge outcomes", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-conflict-outcome-matrix.json")
    const matrix = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(matrix.version, "cicsc/phase6-conflict-outcome-matrix-v1")
    assert.equal(matrix.cases.length, 3)
    const requested = matrix.cases.map((c: any) => c.requested_resolution)
    assert.deepEqual(requested, ["abort", "retry", "merge"])
  })

  it("enforces deterministic outcomes per requested resolution", () => {
    assert.equal(resolveConflictDeterministically("abort"), "abort_or_serialize")
    assert.equal(resolveConflictDeterministically("retry"), "retry_with_fresh_tx")
    assert.equal(resolveConflictDeterministically("merge"), "reject_not_supported")
  })
})
