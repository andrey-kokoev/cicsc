#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase30-objective-verdict-report.json}"

cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const load = (p) => JSON.parse(fs.readFileSync(path.resolve(p), 'utf8'))

const assertions = load('docs/pilot/phase30-objective-verdict-assertions.json')
const run = load('docs/pilot/phase30-objective-closure-run.json')
const c1 = load('docs/pilot/phase7-concurrency-adversarial.json')
const c2a = load('docs/pilot/phase10-parity-continuity.json')
const c2b = load('docs/pilot/category-model-conformance.json')
const c3 = load('docs/pilot/phase11-dsl-usability-evidence.json')
const c4a = load('docs/pilot/phase7-migration-protocol-check.json')
const c4b = load('docs/pilot/phase10-migration-continuity.json')
const c5 = load('docs/pilot/phase12-parity-envelope-differentials.json')

const checks = {
  OBJ1: c1.overall === 'pass',
  OBJ2: c2a.overall === 'pass' && c2b.status === 'pass',
  OBJ3: c3.overall === 'pass',
  OBJ4: c4a.overall === 'pass' && c4b.overall === 'pass',
  OBJ5: c5.overall === 'pass',
}

const objectives = assertions.objective_verdict_contract.map((obj) => {
  const met = Boolean(checks[obj.objective_id])
  return {
    objective_id: obj.objective_id,
    title: obj.title,
    verdict: met ? 'met' : 'not_met',
    assertion: obj.assertion,
    evidence: obj.required_artifacts,
    failure_localization: met ? [] : [`${obj.objective_id}_evidence_not_pass`],
  }
})

const allMet = objectives.every((o) => o.verdict === 'met')
const report = {
  version: 'cicsc/phase30-objective-verdict-report-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  inputs: {
    assertions: 'docs/pilot/phase30-objective-verdict-assertions.json',
    closure_run: 'docs/pilot/phase30-objective-closure-run.json',
    objective_model: 'control-plane/objectives/objective-model.yaml',
  },
  closure_run_overall: run.overall,
  objectives,
  overall_verdict: allMet ? 'met' : 'not_met',
  completion_claim_allowed: allMet,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase30 objective verdict report written: ${outPath}`)
process.exit(allMet ? 0 : 1)
NODE
