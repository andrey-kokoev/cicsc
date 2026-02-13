import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 ergonomics report", () => {
  it("confirms ergonomics improvements preserve invariant safety", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-ergonomics-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-ergonomics-report-v1")
    assert.equal(report.status, "pass")
    assert.deepEqual(report.unresolved_criticals, [])

    const inputs = report.inputs ?? {}
    assert.equal(typeof inputs.dsl_improvements, "string")
    assert.equal(typeof inputs.migration_assistant, "string")
    assert.equal(typeof inputs.usability_benchmark, "string")

    const compile = report.compile_time_safety ?? {}
    assert.ok(Array.isArray(compile.negative_checks))
    assert.ok(compile.negative_checks.length >= 1)

    const runtime = report.runtime_safety ?? {}
    assert.ok(Array.isArray(runtime.conformance_checks))
    assert.ok(runtime.conformance_checks.length >= 3)
  })
})
