#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase12-baseline-continuity.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const phase11Closure = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase11-exit-checklist.json'), 'utf8'))
const phase12Gate = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase12-gate.json'), 'utf8'))
const parity = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase10-parity-continuity.json'), 'utf8'))
const migration = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase10-migration-continuity.json'), 'utf8'))
const ops = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase10-operational-slo-continuity.json'), 'utf8'))

const checks = {
  phase11_exit_checklist: {
    basis: 'docs/pilot/phase11-exit-checklist.json',
    status: (phase11Closure.items ?? []).every((i) => i.status === 'pass') ? 'pass' : 'fail',
  },
  phase12_gate_open: {
    basis: 'docs/pilot/phase12-gate.json',
    status: phase12Gate.blocked === false ? 'pass' : 'fail',
  },
  parity_continuity: {
    basis: 'docs/pilot/phase10-parity-continuity.json',
    status: parity.overall === 'pass' ? 'pass' : 'fail',
  },
  migration_continuity: {
    basis: 'docs/pilot/phase10-migration-continuity.json',
    status: migration.overall === 'pass' ? 'pass' : 'fail',
  },
  operational_slo_continuity: {
    basis: 'docs/pilot/phase10-operational-slo-continuity.json',
    status: ops.overall === 'pass' ? 'pass' : 'fail',
  },
}

const overall = Object.values(checks).every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase12-baseline-continuity-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase12 baseline continuity report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
