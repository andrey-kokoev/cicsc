#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase35-objective-verdict-report.json}"

cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const load = (p) => {
  if (!fs.existsSync(path.resolve(p))) {
    console.error(`Missing required artifact: ${p}`)
    return { status: 'fail', error: 'missing' }
  }
  return JSON.parse(fs.readFileSync(path.resolve(p), 'utf8'))
}

// Phase 32 Expanded Envelopes
const obj1 = load('docs/pilot/phase32-obj1-concurrency-envelope.json')
const obj2 = load('docs/pilot/phase32-obj2-drift-budget.json')
const obj3 = load('docs/pilot/phase32-obj3-usability-envelope.json')
const obj4 = load('docs/pilot/phase32-obj4-migration-envelope.json')
const obj5 = load('docs/pilot/phase32-obj5-parity-envelope.json')

// Phase 34 Multi-Context closure
const p34 = load('docs/pilot/phase34-exit-checklist.json')

const objectiveVerdict = [
  {
    id: 'OBJ1',
    title: 'Invariants Hold Under Concurrency (Expanded)',
    status: (obj1.overall === 'pass' || obj1.status === 'pass') ? 'met' : 'not_met',
    artifact: 'docs/pilot/phase32-obj1-concurrency-envelope.json'
  },
  {
    id: 'OBJ2',
    title: 'IR and Runtime Semantics Align (Expanded)',
    status: (obj2.overall === 'pass' || obj2.status === 'pass') ? 'met' : 'not_met',
    artifact: 'docs/pilot/phase32-obj2-drift-budget.json'
  },
  {
    id: 'OBJ3',
    title: 'Spec DSL Is Usable (Expanded)',
    status: (obj3.overall === 'pass' || obj3.status === 'pass') ? 'met' : 'not_met',
    artifact: 'docs/pilot/phase32-obj3-usability-envelope.json'
  },
  {
    id: 'OBJ4',
    title: 'Migrations Are Replay-Verified (Expanded)',
    status: (obj4.overall === 'pass' || obj4.status === 'pass') ? 'met' : 'not_met',
    artifact: 'docs/pilot/phase32-obj4-migration-envelope.json'
  },
  {
    id: 'OBJ5',
    title: 'Backends Are Oracle-Equivalent (Expanded)',
    status: (obj5.overall === 'pass' || obj5.status === 'pass') ? 'met' : 'not_met',
    artifact: 'docs/pilot/phase32-obj5-parity-envelope.json'
  },
  {
    id: 'P34-VAL',
    title: 'Multi-Context Validation (Phase 34)',
    status: (p34.overall === 'pass' || p34.status === 'pass') ? 'met' : 'not_met',
    artifact: 'docs/pilot/phase34-exit-checklist.json'
  }
]

const allMet = objectiveVerdict.every(v => v.status === 'met')

const report = {
  version: 'cicsc/phase35-objective-verdict-report-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  objectives: objectiveVerdict,
  overall_verdict: allMet ? 'met' : 'not_met'
}

fs.writeFileSync(outPath, JSON.stringify(report, null, 2) + '\n', 'utf8')
console.log(`Phase 35 objective verdict report written to ${outPath}`)
process.exit(allMet ? 0 : 1)
NODE
