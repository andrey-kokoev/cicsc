#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const errors = []
const checkboxRe = /^- \[[ x]\]\s+/m

const forbiddenCheckboxFiles = [
  'PHASE_LEVEL_ROADMAP.md',
  'JOURNEY_VECTOR.md',
  'docs/pilot/canonical-execution-ledger.md',
]

for (const rel of forbiddenCheckboxFiles) {
  const p = path.resolve(rel)
  if (!fs.existsSync(p)) continue
  const txt = fs.readFileSync(p, 'utf8')
  if (checkboxRe.test(txt)) errors.push(`${rel}: contains markdown checkboxes but is non-canonical`) 
}

const phaseLevel = path.resolve('PHASE_LEVEL_ROADMAP.md')
if (fs.existsSync(phaseLevel)) {
  const txt = fs.readFileSync(phaseLevel, 'utf8')
  if (!txt.includes('Canonical status truth remains `control-plane/execution/execution-ledger.yaml` only.')) {
    errors.push('PHASE_LEVEL_ROADMAP.md: missing canonical truth disclaimer')
  }
}

if (errors.length) {
  console.error('workflow single-source check failed')
  for (const e of errors) console.error(`- ${e}`)
  process.exit(1)
}

console.log('workflow single-source check passed')
NODE
