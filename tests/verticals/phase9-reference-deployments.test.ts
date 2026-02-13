import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 reference deployments", () => {
  it("freezes at least two deployment verticals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-reference-deployments.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-reference-deployments-v1")
    assert.equal(report.status, "pass")
    assert.ok(Array.isArray(report.deployments))
    assert.ok(report.deployments.length >= 2)
    const names = report.deployments.map((d: any) => d.vertical)
    assert.ok(names.includes("ticketing"))
    assert.ok(names.includes("crm"))
  })
})
