#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase13-baseline-continuity.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const phase12Checklist = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase12-exit-checklist.json'), 'utf8'))
const phase13Gate = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase13-gate.json'), 'utf8'))
const parity = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase12-parity-envelope-differentials.json'), 'utf8'))
const deployment = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase12-deployment-expansion-report.json'), 'utf8'))

const checks = {
  phase12_exit_checklist: {
    basis: 'docs/pilot/phase12-exit-checklist.json',
    status: (phase12Checklist.items ?? []).every((i) => i.status === 'pass') ? 'pass' : 'fail',
  },
  phase13_gate_open: {
    basis: 'docs/pilot/phase13-gate.json',
    status: phase13Gate.blocked === false ? 'pass' : 'fail',
  },
  parity_envelope_continuity: {
    basis: 'docs/pilot/phase12-parity-envelope-differentials.json',
    status: parity.overall === 'pass' ? 'pass' : 'fail',
  },
  deployment_expansion_continuity: {
    basis: 'docs/pilot/phase12-deployment-expansion-report.json',
    status: deployment.status === 'pass' ? 'pass' : 'fail',
  },
}

const overall = Object.values(checks).every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase13-baseline-continuity-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase13 baseline continuity report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
