#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase34-expanded-multi-context-required-gates.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const requiredArtifacts = [
  { id: 'context_matrix', path: 'docs/pilot/phase34-context-matrix.json' },
  { id: 'acceptance_contract', path: 'docs/pilot/phase34-acceptance-contract.json' },
  { id: 'multi_context_workloads', path: 'docs/pilot/phase34-multi-context-workloads.json' },
  { id: 'drift_localization_report', path: 'docs/pilot/phase34-drift-localization-report.json' },
]

const checks = requiredArtifacts.map((a) => {
  const abs = path.resolve(a.path)
  const exists = fs.existsSync(abs)
  let status = 'fail'
  let detail = 'missing_artifact'
  if (exists) {
    try {
      const j = JSON.parse(fs.readFileSync(abs, 'utf8'))
      // Check for .status === 'pass' or .overall === 'pass'
      const val = j.status ?? j.overall
      status = val === 'pass' ? 'pass' : 'fail'
      detail = `${val ? 'status' : 'unknown'}=${val ?? 'missing'}`
    } catch (_err) {
      status = 'fail'
      detail = 'invalid_json'
    }
  }
  return { id: a.id, artifact: a.path, status, detail }
})

const overall = checks.every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase34-expanded-multi-context-required-gates-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase34 expanded multi-context required gates report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
