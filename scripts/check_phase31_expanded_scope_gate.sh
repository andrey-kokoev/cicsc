#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase31-expanded-scope-gate.json}"

cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const required = [
  'docs/pilot/phase31-era2-completion-target.json',
  'docs/pilot/phase31-objective-extension-contract.json',
  'docs/pilot/phase31-proof-evidence-coupling-plan.json',
]

const checks = required.map((p) => {
  const abs = path.resolve(p)
  const ok = fs.existsSync(abs)
  return { artifact: p, status: ok ? 'pass' : 'fail' }
})

const overall = checks.every((c) => c.status === 'pass') ? 'pass' : 'fail'
const report = {
  version: 'cicsc/phase31-expanded-scope-gate-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  overall,
  checks,
  policy: 'phase31_closure_requires_target_extension_and_coupling_contracts',
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase31 expanded scope gate written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
