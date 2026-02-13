import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase12 parity envelope differentials", () => {
  it("records pass coverage for all envelope harness checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase12-parity-envelope-differentials.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase12-parity-envelope-differentials-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.having_exec_vs_oracle.status, "pass")
    assert.equal(r.checks.postgres_having_harness.status, "pass")
    assert.equal(r.checks.exists_negative_gate.status, "pass")
    assert.equal(r.checks.random_differential_sweeps.status, "pass")
  })
})
