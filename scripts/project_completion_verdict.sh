#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH_JSON="${1:-${ROOT_DIR}/docs/pilot/project-completion-verdict-report.json}"
OUT_PATH_MD="${2:-${ROOT_DIR}/docs/pilot/project-completion-verdict-report.md}"

cd "${ROOT_DIR}"

node - "${OUT_PATH_JSON}" "${OUT_PATH_MD}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPathJson = process.argv[2]
const outPathMd = process.argv[3]
const load = (p) => JSON.parse(fs.readFileSync(path.resolve(p), 'utf8'))

const verdictReport = load('docs/pilot/phase35-objective-verdict-report.json')
const forcedNext = load('docs/pilot/phase35-forced-next-disposition.json')

const overallSafeToComplete = verdictReport.overall_verdict === 'met' && forcedNext.completion_claim_blocked === false

const finalReport = {
  version: 'cicsc/project-completion-verdict-report-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  summary: {
    status: overallSafeToComplete ? 'completed' : 'blocked',
    verdict: verdictReport.overall_verdict,
    forced_next_required: forcedNext.forced_next_required
  },
  objectives: verdictReport.objectives,
  inputs: {
    phase35_verdict: 'docs/pilot/phase35-objective-verdict-report.json',
    forced_next_disposition: 'docs/pilot/phase35-forced-next-disposition.json'
  }
}

fs.writeFileSync(outPathJson, JSON.stringify(finalReport, null, 2) + '\n', 'utf8')

let md = `# Project Completion Verdict Report\n\n`
md += `**Timestamp:** ${new Date().toISOString()}\n`
md += `**Overall Status:** ${overallSafeToComplete ? '✅ COMPLETED' : '❌ BLOCKED'}\n\n`
md += `## Objective Status\n\n`
md += `| ID | Title | Status | Evidence |\n`
md += `|---|---|---|---|\n`
verdictReport.objectives.forEach(obj => {
  md += `| ${obj.id} | ${obj.title} | ${obj.status === 'met' ? '✅ MET' : '❌ NOT MET'} | [${path.basename(obj.artifact)}](${obj.artifact}) |\n`
})
md += `\n## Disposition\n\n`
md += `- Forced-next required: ${forcedNext.forced_next_required ? 'YES' : 'NO'}\n`
md += `- Completion claim allowed: ${overallSafeToComplete ? 'YES' : 'NO'}\n`

fs.writeFileSync(outPathMd, md, 'utf8')

console.log(`Project completion verdict reports written to ${outPathJson} and ${outPathMd}`)
process.exit(overallSafeToComplete ? 0 : 1)
NODE
