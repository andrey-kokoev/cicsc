#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase15-baseline-continuity.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const phase14Checklist = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase14-exit-checklist.json'), 'utf8'))
const phase15Gate = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase15-gate.json'), 'utf8'))
const generalization = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase14-generalization-envelope-report.json'), 'utf8'))
const readiness = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase14-readiness-closure-report.json'), 'utf8'))

const checks = {
  phase14_exit_checklist: {
    basis: 'docs/pilot/phase14-exit-checklist.json',
    status: (phase14Checklist.items ?? []).every((i) => i.status === 'pass') ? 'pass' : 'fail',
  },
  phase15_gate_open: {
    basis: 'docs/pilot/phase15-gate.json',
    status: phase15Gate.blocked === false ? 'pass' : 'fail',
  },
  generalization_continuity: {
    basis: 'docs/pilot/phase14-generalization-envelope-report.json',
    status: generalization.status === 'pass' ? 'pass' : 'fail',
  },
  readiness_continuity: {
    basis: 'docs/pilot/phase14-readiness-closure-report.json',
    status: readiness.status === 'pass' ? 'pass' : 'fail',
  },
}

const overall = Object.values(checks).every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase15-baseline-continuity-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase15 baseline continuity report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
