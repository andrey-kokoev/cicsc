import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 resilience slo gate", () => {
  it("records green verify/migrate/command path checks with zero-failure budget", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-resilience-slo.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase8-resilience-slo-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.verify_path.status, "pass")
    assert.equal(r.checks.migrate_path.status, "pass")
    assert.equal(r.checks.command_path.status, "pass")
    assert.equal(r.error_budget.verify_path_failures_per_window, 0)
  })
})
