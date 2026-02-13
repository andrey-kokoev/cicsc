import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 operational resilience contract", () => {
  it("declares resilience guarantees and bounded recovery windows", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-operational-resilience-contract.json")
    const c = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(c.version, "cicsc/phase8-operational-resilience-contract-v1")
    assert.ok(c.guarantees.length >= 3)
    assert.equal(typeof c.recovery_windows.verify, "string")
    assert.ok(c.preserved_exclusions.includes("no distributed transactions across tenants"))
  })
})
