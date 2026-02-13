import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase5 migration drill evidence", () => {
  it("links runbook and drill artifacts with passing status", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase5-migration-drill-evidence.json")
    const evidence = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(evidence.version, "cicsc/phase5-migration-drill-evidence-v1")
    assert.equal(evidence.status, "pass")
    assert.equal(fs.existsSync(path.resolve(process.cwd(), evidence.runbook)), true)
    for (const artifact of evidence.drill_artifacts ?? []) {
      assert.equal(fs.existsSync(path.resolve(process.cwd(), artifact)), true)
    }
  })
})
