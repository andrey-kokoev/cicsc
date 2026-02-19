import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { existsSync, readFileSync } from "node:fs"
import path from "node:path"

const fixtureRoot = "tests/fixtures/executable-surface"

function runCase(caseName: string) {
  const policyPath = path.resolve(process.cwd(), fixtureRoot, caseName, "policy.json")
  const reportPath = path.resolve(process.cwd(), "state", `executable-surface-${caseName}.json`)
  const run = spawnSync(
    "./scripts/check_executable_surface_integrity.sh",
    ["--policy", policyPath, "--json", reportPath],
    {
      cwd: process.cwd(),
      encoding: "utf8",
    },
  )

  const report = existsSync(reportPath)
    ? JSON.parse(readFileSync(reportPath, "utf8"))
    : { violations: [] }

  return { run, report }
}

function hasKind(report: any, kind: string): boolean {
  return (report.violations ?? []).some((v: any) => v.kind === kind)
}

describe("executable surface integrity gate", () => {
  it("passes when executable refs are valid", () => {
    const { run } = runCase("pass_valid")
    assert.equal(run.status, 0, run.stderr || run.stdout)
  })

  it("fails on missing path in shell surface", () => {
    const { run, report } = runCase("fail_missing_shell")
    assert.notEqual(run.status, 0)
    assert.equal(hasKind(report, "missing_path"), true)
  })

  it("fails on missing path in test surface", () => {
    const { run, report } = runCase("fail_missing_ts")
    assert.notEqual(run.status, 0)
    assert.equal(hasKind(report, "missing_path"), true)
  })

  it("fails on banned runtime yaml reference", () => {
    const { run, report } = runCase("fail_banned_yaml")
    assert.notEqual(run.status, 0)
    assert.equal(hasKind(report, "non_canonical_runtime_source"), true)
  })

  it("fails on generated reference without contract", () => {
    const { run, report } = runCase("fail_generated_no_contract")
    assert.notEqual(run.status, 0)
    assert.equal(hasKind(report, "generated_ref_without_contract"), true)
  })

  it("passes with non-expired allowlist match", () => {
    const { run, report } = runCase("pass_allowlisted")
    assert.equal(run.status, 0, run.stderr || run.stdout)
    assert.equal((report.violations ?? []).some((v: any) => v.allowlisted === true), true)
  })

  it("fails with expired allowlist entry", () => {
    const { run, report } = runCase("fail_expired_allowlist")
    assert.notEqual(run.status, 0)
    assert.equal(hasKind(report, "stale_allowlist_entry"), true)
  })

  it("fails with stale unmatched allowlist entry", () => {
    const { run, report } = runCase("fail_stale_allowlist")
    assert.notEqual(run.status, 0)
    assert.equal(hasKind(report, "stale_allowlist_entry"), true)
  })

  it("fails when allowlist metadata is missing required fields", () => {
    const { run, report } = runCase("fail_allowlist_missing_metadata")
    assert.notEqual(run.status, 0)
    assert.equal(hasKind(report, "stale_allowlist_entry"), true)
  })
})
