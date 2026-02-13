import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 migration protocol contract", () => {
  it("extends migration protocol with phase9 sql-surface controls", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-migration-protocol-contract.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-migration-protocol-contract-v1")
    assert.equal(report.status, "pass")
    assert.ok(report.extended_for_phase9.sql_surface.includes("having_enabled"))
    assert.ok(report.extended_for_phase9.sql_surface.includes("exists_deferred"))
    assert.ok((report.extended_for_phase9.required_preflight_checks ?? []).length >= 4)
    assert.ok((report.extended_for_phase9.required_cutover_checks ?? []).length >= 3)
  })
})
