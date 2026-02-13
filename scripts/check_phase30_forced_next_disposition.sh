#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase30-forced-next-disposition.json}"

cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const verdictPath = 'docs/pilot/phase30-objective-verdict-report.json'
const verdict = JSON.parse(fs.readFileSync(path.resolve(verdictPath), 'utf8'))

const notMet = (verdict.objectives ?? []).filter((o) => o.verdict === 'not_met')
const forcedNextRequired = notMet.length > 0

const report = {
  version: 'cicsc/phase30-forced-next-disposition-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  inputs: {
    objective_verdict_report: verdictPath,
    execution_ledger: 'control-plane/execution/execution-ledger.yaml',
  },
  overall_verdict: verdict.overall_verdict,
  forced_next_required: forcedNextRequired,
  completion_claim_blocked: forcedNextRequired,
  derived_forced_next_checkboxes: forcedNextRequired
    ? notMet.map((o, i) => ({
        id: `AU2.${i + 1}`,
        title: `Close objective gap for ${o.objective_id}: ${o.failure_localization.join(', ') || 'unspecified'}`,
      }))
    : [],
  policy: forcedNextRequired
    ? 'block_completion_and_derive_forced_next_only'
    : 'allow_completion_no_forced_next_required',
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase30 forced-next disposition written: ${outPath}`)
process.exit(0)
NODE
