import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 migration protocol contract", () => {
  it("defines executable migration protocol policy and green protocol check", () => {
    const contractPath = path.resolve(process.cwd(), "docs/pilot/phase7-migration-protocol-contract.json")
    const checkPath = path.resolve(process.cwd(), "docs/pilot/phase7-migration-protocol-check.json")
    const contract = JSON.parse(fs.readFileSync(contractPath, "utf8"))
    const check = JSON.parse(fs.readFileSync(checkPath, "utf8"))

    assert.equal(contract.version, "cicsc/phase7-migration-protocol-contract-v1")
    assert.equal(contract.policy.preflight_required, true)
    assert.equal(contract.policy.rollback_mandatory_on_verify_fail, true)
    assert.equal(check.version, "cicsc/phase7-migration-protocol-check-v1")
    assert.equal(check.overall, "pass")
  })
})
