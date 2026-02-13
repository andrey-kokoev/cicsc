import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("category model conformance gate", () => {
  it("passes obligation checks and emits pass report", () => {
    const run = spawnSync("./scripts/check_category_model_conformance.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)

    const rp = path.resolve(process.cwd(), "docs/pilot/category-model-conformance.json")
    const report = JSON.parse(fs.readFileSync(rp, "utf8"))
    assert.equal(report.version, "cicsc/category-model-conformance-v1")
    assert.equal(report.status, "pass")
    assert.ok(Array.isArray(report.obligations))
    assert.ok(report.obligations.length >= 5)
  })
})
