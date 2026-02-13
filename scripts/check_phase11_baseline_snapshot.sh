#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase11-baseline-gates.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const outPath = process.argv[2]

function load(p) {
  return JSON.parse(fs.readFileSync(path.resolve(p), "utf8"))
}

const parity = load("docs/pilot/phase10-parity-continuity.json")
const migration = load("docs/pilot/phase10-migration-continuity.json")
const ops = load("docs/pilot/phase10-operational-slo-continuity.json")
const governance = load("docs/pilot/phase10-doc-consistency.json")
const phase11Gate = load("docs/pilot/phase11-gate.json")

const checks = {
  parity_continuity: {
    basis: "docs/pilot/phase10-parity-continuity.json",
    status: parity.overall === "pass" ? "pass" : "fail",
  },
  migration_continuity: {
    basis: "docs/pilot/phase10-migration-continuity.json",
    status: migration.overall === "pass" ? "pass" : "fail",
  },
  operational_slo_continuity: {
    basis: "docs/pilot/phase10-operational-slo-continuity.json",
    status: ops.overall === "pass" ? "pass" : "fail",
  },
  governance_drift_gate: {
    basis: "docs/pilot/phase10-doc-consistency.json",
    status: governance.status === "pass" ? "pass" : "fail",
  },
  phase11_block_gate: {
    basis: "docs/pilot/phase11-gate.json",
    status: phase11Gate.blocked === false ? "pass" : "fail",
  },
}

const overall = Object.values(checks).every((c) => c.status === "pass") ? "pass" : "fail"

const report = {
  version: "cicsc/phase11-baseline-gates-v1",
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, "utf8")
console.log(`phase11 baseline gate snapshot written: ${outPath}`)
process.exit(overall === "pass" ? 0 : 1)
NODE
