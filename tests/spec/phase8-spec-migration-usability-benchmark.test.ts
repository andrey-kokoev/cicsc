import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

describe("phase8 spec/migration usability benchmark", () => {
  it("publishes multi-vertical benchmark artifact with pass status", () => {
    const run = spawnSync("./scripts/phase8_spec_migration_usability_benchmark.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)

    const p = path.resolve(process.cwd(), "docs/pilot/phase8-spec-migration-usability-benchmark.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-spec-migration-usability-benchmark-v1")
    assert.ok(Array.isArray(report.verticals))
    assert.ok(report.verticals.length >= 3)
    for (const v of report.verticals) {
      assert.equal(v.status, "pass")
      assert.ok(v.entity_count >= 1)
      assert.ok(v.transform_count >= 1)
      assert.ok(v.state_map_count >= 1)
    }

    assert.equal(report.summary.total_verticals, report.verticals.length)
    assert.equal(report.summary.passing_verticals, report.verticals.length)
    assert.deepEqual(report.summary.failing_verticals, [])
  })
})
