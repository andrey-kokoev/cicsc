#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase36-collaboration-theorems.json}"
cd "${ROOT_DIR}"

LEAN_FILE="lean/Cicsc/Evolution/Collaboration.lean"

node - "${OUT_PATH}" "${LEAN_FILE}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const leanFile = process.argv[3]

const requiredTheorems = [
  'no_sent_fulfilled_skip',
  'fulfilled_from_inProgress',
  'close_requires_precondition',
  'closed_to_ingested_monotone',
  'rescind_admissibility',
  'rescinded_is_terminal'
]

const results = []
let overall = 'pass'

if (!fs.existsSync(leanFile)) {
  overall = 'fail'
  results.push({ check: 'file_exists', status: 'fail', error: `Lean file ${leanFile} not found` })
} else {
  const content = fs.readFileSync(leanFile, 'utf8')
  for (const th of requiredTheorems) {
    const found = content.includes(`theorem ${th}`)
    if (!found) {
      overall = 'fail'
      results.push({ check: `theorem_${th}_present`, status: 'fail' })
    } else {
      results.push({ check: `theorem_${th}_present`, status: 'pass' })
    }
  }
}

const report = {
  version: 'cicsc/phase36-collaboration-theorems-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  theorems: results
}

fs.writeFileSync(outPath, JSON.stringify(report, null, 2) + '\n', 'utf8')
console.log(`Phase 36 collaboration theorems report written to ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
