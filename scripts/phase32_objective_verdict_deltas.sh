#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase32-expanded-scope-closure-report.json}"

cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const loadJson = (p) => JSON.parse(fs.readFileSync(path.resolve(p), 'utf8'))
const safeOverall = (p) => {
  const abs = path.resolve(p)
  if (!fs.existsSync(abs)) return 'missing'
  try {
    const j = JSON.parse(fs.readFileSync(abs, 'utf8'))
    return j.overall ?? 'unknown'
  } catch {
    return 'invalid'
  }
}

const baseline = loadJson('docs/pilot/phase30-objective-verdict-report.json')
const current = {
  OBJ1: safeOverall('docs/pilot/phase32-obj1-concurrency-envelope.json'),
  OBJ2: safeOverall('docs/pilot/phase32-obj2-drift-budget.json'),
  OBJ3: safeOverall('docs/pilot/phase32-obj3-usability-envelope.json'),
  OBJ4: safeOverall('docs/pilot/phase32-obj4-migration-envelope.json'),
  OBJ5: safeOverall('docs/pilot/phase32-obj5-parity-envelope.json'),
}

const baselineByObj = {}
for (const o of baseline.objectives ?? []) baselineByObj[o.objective_id] = o.verdict

const objectives = ['OBJ1', 'OBJ2', 'OBJ3', 'OBJ4', 'OBJ5'].map((id) => {
  const now = current[id]
  const currentVerdict = now === 'pass' ? 'met' : 'not_met'
  const prior = baselineByObj[id] ?? 'unknown'
  const delta = prior === currentVerdict ? 'no_change' : `${prior}_to_${currentVerdict}`
  return {
    objective_id: id,
    baseline_verdict: prior,
    current_signal: now,
    current_verdict: currentVerdict,
    delta,
  }
})

const allMet = objectives.every((o) => o.current_verdict === 'met')
const report = {
  version: 'cicsc/phase32-expanded-scope-closure-report-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  inputs: {
    baseline_verdict: 'docs/pilot/phase30-objective-verdict-report.json',
    obj1: 'docs/pilot/phase32-obj1-concurrency-envelope.json',
    obj2: 'docs/pilot/phase32-obj2-drift-budget.json',
    obj3: 'docs/pilot/phase32-obj3-usability-envelope.json',
    obj4: 'docs/pilot/phase32-obj4-migration-envelope.json',
    obj5: 'docs/pilot/phase32-obj5-parity-envelope.json',
  },
  objectives,
  overall: allMet ? 'pass' : 'fail',
  completion_readiness: allMet ? 'ready_for_phase32_exit' : 'blocked_pending_remaining_objectives',
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase32 expanded-scope closure report written: ${outPath}`)
process.exit(0)
NODE
