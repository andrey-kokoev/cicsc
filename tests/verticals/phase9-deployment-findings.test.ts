import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 deployment findings", () => {
  it("captures findings with required severity/status labels", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-deployment-findings.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-deployment-findings-v1")
    const findings = report.findings ?? []
    assert.ok(findings.length >= 3)
    for (const f of findings) {
      assert.equal(typeof f.id, "string")
      assert.ok(["low", "medium", "high", "critical"].includes(f.severity))
      assert.ok(["closed", "deferred"].includes(f.status))
    }
  })
})
