#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase16-baseline-continuity.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const phase15Checklist = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase15-exit-checklist.json'), 'utf8'))
const phase16Gate = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase16-gate.json'), 'utf8'))
const objective = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase15-objective-closure-report.json'), 'utf8'))
const surface = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase15-deferred-surface-closure-report.json'), 'utf8'))

const checks = {
  phase15_exit_checklist: {
    basis: 'docs/pilot/phase15-exit-checklist.json',
    status: (phase15Checklist.items ?? []).every((i) => i.status === 'pass') ? 'pass' : 'fail',
  },
  phase16_gate_open: {
    basis: 'docs/pilot/phase16-gate.json',
    status: phase16Gate.blocked === false ? 'pass' : 'fail',
  },
  objective_continuity: {
    basis: 'docs/pilot/phase15-objective-closure-report.json',
    status: objective.status === 'pass' ? 'pass' : 'fail',
  },
  deferred_surface_continuity: {
    basis: 'docs/pilot/phase15-deferred-surface-closure-report.json',
    status: surface.status === 'pass' ? 'pass' : 'fail',
  },
}

const overall = Object.values(checks).every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase16-baseline-continuity-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase16 baseline continuity report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
