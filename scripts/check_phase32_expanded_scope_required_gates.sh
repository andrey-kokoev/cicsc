#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase32-expanded-scope-required-gates.json}"

cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const requiredArtifacts = [
  { id: 'obj1_concurrency_envelope', path: 'docs/pilot/phase32-obj1-concurrency-envelope.json' },
  { id: 'obj2_drift_budget', path: 'docs/pilot/phase32-obj2-drift-budget.json' },
  { id: 'obj3_usability_envelope', path: 'docs/pilot/phase32-obj3-usability-envelope.json' },
  { id: 'obj4_migration_envelope', path: 'docs/pilot/phase32-obj4-migration-envelope.json' },
  { id: 'obj5_parity_envelope', path: 'docs/pilot/phase32-obj5-parity-envelope.json' },
]

const checks = requiredArtifacts.map((a) => {
  const abs = path.resolve(a.path)
  const exists = fs.existsSync(abs)
  let status = 'fail'
  let detail = 'missing_artifact'
  if (exists) {
    try {
      const j = JSON.parse(fs.readFileSync(abs, 'utf8'))
      status = j.overall === 'pass' ? 'pass' : 'fail'
      detail = `overall=${j.overall ?? 'unknown'}`
    } catch (_err) {
      status = 'fail'
      detail = 'invalid_json'
    }
  }
  return { id: a.id, artifact: a.path, status, detail }
})

const overall = checks.every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase32-expanded-scope-required-gates-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase32 expanded-scope required gates report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
