import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 concurrency contract delta", () => {
  it("declares explicit strengthened guarantees over phase6 baseline", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-concurrency-contract-delta.json")
    const delta = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(delta.version, "cicsc/phase7-concurrency-contract-delta-v1")
    assert.equal(delta.baseline_contract, "docs/pilot/phase6-concurrency-contract.json")
    assert.ok(delta.delta.strengthened_guarantees.length >= 3)
    assert.ok(delta.delta.preserved_exclusions.includes("no distributed transaction guarantee"))
  })
})
