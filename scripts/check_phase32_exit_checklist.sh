#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase32-exit-checklist.json}"

cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const load = (p) => JSON.parse(fs.readFileSync(path.resolve(p), 'utf8'))
const safeOverall = (p) => {
  const abs = path.resolve(p)
  if (!fs.existsSync(abs)) return 'missing'
  try { return (JSON.parse(fs.readFileSync(abs, 'utf8')).overall ?? 'unknown') } catch { return 'invalid' }
}

const objArtifacts = [
  'docs/pilot/phase32-obj1-concurrency-envelope.json',
  'docs/pilot/phase32-obj2-drift-budget.json',
  'docs/pilot/phase32-obj3-usability-envelope.json',
  'docs/pilot/phase32-obj4-migration-envelope.json',
  'docs/pilot/phase32-obj5-parity-envelope.json',
]
const objPass = objArtifacts.every((p) => safeOverall(p) === 'pass')
const gates = safeOverall('docs/pilot/phase32-expanded-scope-required-gates.json')
const closureExists = fs.existsSync(path.resolve('docs/pilot/phase32-expanded-scope-closure-report.json'))

const report = {
  version: 'cicsc/phase32-exit-checklist-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  phase: 32,
  items: [
    {
      id: 'phase32_obj_envelopes',
      description: 'OBJ1-OBJ5 expanded envelope artifacts exist and pass.',
      status: objPass ? 'pass' : 'fail',
      artifacts: objArtifacts,
    },
    {
      id: 'phase32_required_gates',
      description: 'Expanded-scope required-gates contract report is pass.',
      status: gates === 'pass' ? 'pass' : 'fail',
      artifacts: ['docs/pilot/phase32-expanded-scope-required-gates.json'],
    },
    {
      id: 'phase32_closure_report',
      description: 'Expanded-scope closure report with objective deltas is published.',
      status: closureExists ? 'pass' : 'fail',
      artifacts: ['docs/pilot/phase32-expanded-scope-closure-report.json'],
    },
  ],
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase32 exit checklist written: ${outPath}`)
process.exit(report.items.every((i) => i.status === 'pass') ? 0 : 1)
NODE
