#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase14-baseline-continuity.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const phase13Checklist = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase13-exit-checklist.json'), 'utf8'))
const phase14Gate = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase14-gate.json'), 'utf8'))
const scale = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase13-scale-envelope-report.json'), 'utf8'))
const hardening = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase13-hardening-closure-report.json'), 'utf8'))

const checks = {
  phase13_exit_checklist: {
    basis: 'docs/pilot/phase13-exit-checklist.json',
    status: (phase13Checklist.items ?? []).every((i) => i.status === 'pass') ? 'pass' : 'fail',
  },
  phase14_gate_open: {
    basis: 'docs/pilot/phase14-gate.json',
    status: phase14Gate.blocked === false ? 'pass' : 'fail',
  },
  scale_continuity: {
    basis: 'docs/pilot/phase13-scale-envelope-report.json',
    status: scale.status === 'pass' ? 'pass' : 'fail',
  },
  hardening_continuity: {
    basis: 'docs/pilot/phase13-hardening-closure-report.json',
    status: hardening.status === 'pass' ? 'pass' : 'fail',
  },
}

const overall = Object.values(checks).every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase14-baseline-continuity-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase14 baseline continuity report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
