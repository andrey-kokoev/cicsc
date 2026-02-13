#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase17-baseline-continuity.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const phase16Checklist = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase16-exit-checklist.json'), 'utf8'))
const phase17Gate = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase17-gate.json'), 'utf8'))
const extValidation = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase16-external-validation-closure-report.json'), 'utf8'))
const expansionHardening = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase16-expansion-hardening-closure-report.json'), 'utf8'))

const checks = {
  phase16_exit_checklist: {
    basis: 'docs/pilot/phase16-exit-checklist.json',
    status: (phase16Checklist.items ?? []).every((i) => i.status === 'pass') ? 'pass' : 'fail',
  },
  phase17_gate_open: {
    basis: 'docs/pilot/phase17-gate.json',
    status: phase17Gate.blocked === false ? 'pass' : 'fail',
  },
  external_validation_continuity: {
    basis: 'docs/pilot/phase16-external-validation-closure-report.json',
    status: extValidation.status === 'pass' ? 'pass' : 'fail',
  },
  expansion_hardening_continuity: {
    basis: 'docs/pilot/phase16-expansion-hardening-closure-report.json',
    status: expansionHardening.status === 'pass' ? 'pass' : 'fail',
  },
}

const overall = Object.values(checks).every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase17-baseline-continuity-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase17 baseline continuity report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
