#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase19-gate.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const checklistPath = 'docs/pilot/phase18-exit-checklist.json'
const roadmapPath = 'ROADMAP.md'

const checklist = JSON.parse(fs.readFileSync(path.resolve(checklistPath), 'utf8'))
const roadmap = fs.readFileSync(path.resolve(roadmapPath), 'utf8')

const checklistPass = (checklist.items ?? []).every((i) => i.status === 'pass')
const aiMatches = [...roadmap.matchAll(/^- \[(x| )\] AI(\d)\.(\d)\s+/gm)]
const allAiChecked = aiMatches.length > 0 && aiMatches.every((m) => m[1] === 'x')

const blocked = !(checklistPass && allAiChecked)
const reasons = []
if (!checklistPass) reasons.push('phase18_exit_checklist_not_pass')
if (!allAiChecked) reasons.push('roadmap_ai_series_incomplete')

const report = {
  version: 'cicsc/phase19-gate-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  blocked,
  basis: {
    checklist: checklistPath,
    roadmap: roadmapPath,
  },
  reasons,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase19 gate report written: ${outPath}`)
process.exit(blocked ? 1 : 0)
NODE
