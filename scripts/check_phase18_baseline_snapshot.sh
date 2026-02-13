#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase18-baseline-continuity.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const phase17Checklist = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase17-exit-checklist.json'), 'utf8'))
const phase18Gate = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase18-gate.json'), 'utf8'))
const field = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase17-field-program-closure-report.json'), 'utf8'))
const trust = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase17-trust-hardening-closure-report.json'), 'utf8'))

const checks = {
  phase17_exit_checklist: {
    basis: 'docs/pilot/phase17-exit-checklist.json',
    status: (phase17Checklist.items ?? []).every((i) => i.status === 'pass') ? 'pass' : 'fail',
  },
  phase18_gate_open: {
    basis: 'docs/pilot/phase18-gate.json',
    status: phase18Gate.blocked === false ? 'pass' : 'fail',
  },
  field_program_continuity: {
    basis: 'docs/pilot/phase17-field-program-closure-report.json',
    status: field.status === 'pass' ? 'pass' : 'fail',
  },
  trust_hardening_continuity: {
    basis: 'docs/pilot/phase17-trust-hardening-closure-report.json',
    status: trust.status === 'pass' ? 'pass' : 'fail',
  },
}

const overall = Object.values(checks).every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase18-baseline-continuity-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase18 baseline continuity report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
