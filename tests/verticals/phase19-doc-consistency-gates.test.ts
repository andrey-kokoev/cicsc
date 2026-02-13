import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase19 doc consistency gates", () => {
  it("passes status-drift check between PHASE19 and ROADMAP", () => {
    const run = spawnSync("./scripts/check_phase19_docs_consistency.sh", { cwd: process.cwd(), encoding: "utf8" })
    assert.equal(run.status, 0, run.stderr || run.stdout)
    const rp = path.resolve(process.cwd(), "docs/pilot/phase19-doc-consistency.json")
    const report = JSON.parse(fs.readFileSync(rp, "utf8"))
    assert.equal(report.version, "cicsc/phase19-doc-consistency-v1")
    assert.equal(report.status, "pass")
  })
})
