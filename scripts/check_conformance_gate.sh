#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE_PATH="${ROOT_DIR}/tests/conformance/coverage-baseline.json"

if [[ ! -f "${BASELINE_PATH}" ]]; then
  echo "missing coverage baseline: ${BASELINE_PATH}" >&2
  exit 1
fi

node --loader "${ROOT_DIR}/tests/harness/ts-extension-loader.mjs" - "${ROOT_DIR}" "${BASELINE_PATH}" <<'NODE'
const fs = await import("node:fs")
const path = await import("node:path")
const { pathToFileURL } = await import("node:url")

const rootDir = process.argv[2]
const baselinePath = process.argv[3]
const baseline = JSON.parse(fs.readFileSync(baselinePath, "utf-8"))

if (baseline.version !== "cicsc/conformance-coverage-baseline-v1") {
  throw new Error(`unexpected baseline version: ${baseline.version}`)
}

const reportModuleUrl = pathToFileURL(path.join(rootDir, "tests/conformance/operator-coverage-report.ts")).href
const reportMod = await import(reportModuleUrl)
const report = reportMod.generateCoverageReport()

const minCoverage = Number(baseline.minimumCoveragePercent ?? 0)
if (report.summary.coveragePercent < minCoverage) {
  throw new Error(
    `conformance coverage ${report.summary.coveragePercent}% below threshold ${minCoverage}%`
  )
}

const allowed = new Set(baseline.allowedGapOperators ?? [])
const currentGapOps = report.gaps.map((g) => g.operator)
const unexpected = currentGapOps.filter((op) => !allowed.has(op))
if (unexpected.length > 0) {
  throw new Error(`untracked conformance gap(s): ${unexpected.join(", ")}`)
}

console.log(
  `conformance gate passed (coverage=${report.summary.coveragePercent}%, gaps=${currentGapOps.join(", ")})`
)
NODE
