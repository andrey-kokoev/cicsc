#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase35-forced-next-disposition.json}"

cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const load = (p) => JSON.parse(fs.readFileSync(path.resolve(p), 'utf8'))

const verdictReport = load('docs/pilot/phase35-objective-verdict-report.json')

const overallMet = verdictReport.overall_verdict === 'met'

const report = {
  version: 'cicsc/phase35-forced-next-disposition-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  inputs: {
    objective_verdict_report: 'docs/pilot/phase35-objective-verdict-report.json',
  },
  overall_verdict: verdictReport.overall_verdict,
  forced_next_required: !overallMet,
  completion_claim_blocked: !overallMet,
  derived_forced_next_checkboxes: [],
  policy: overallMet ? 'allow_completion_no_forced_next_required' : 'completion_blocked_forced_next_required'
}

fs.writeFileSync(outPath, JSON.stringify(report, null, 2) + '\n', 'utf8')
console.log(`Phase 35 forced-next disposition written to ${outPath}`)
process.exit(overallMet ? 0 : 1)
NODE
