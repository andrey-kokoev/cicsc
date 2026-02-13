#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase18-gate.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const checklistPath = 'docs/pilot/phase17-exit-checklist.json'
const roadmapPath = 'ROADMAP.md'

const checklist = JSON.parse(fs.readFileSync(path.resolve(checklistPath), 'utf8'))
const roadmap = fs.readFileSync(path.resolve(roadmapPath), 'utf8')

const checklistPass = (checklist.items ?? []).every((i) => i.status === 'pass')
const ahMatches = [...roadmap.matchAll(/^- \[(x| )\] AH(\d)\.(\d)\s+/gm)]
const allAhChecked = ahMatches.length > 0 && ahMatches.every((m) => m[1] === 'x')

const blocked = !(checklistPass && allAhChecked)
const reasons = []
if (!checklistPass) reasons.push('phase17_exit_checklist_not_pass')
if (!allAhChecked) reasons.push('roadmap_ah_series_incomplete')

const report = {
  version: 'cicsc/phase18-gate-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  blocked,
  basis: {
    checklist: checklistPath,
    roadmap: roadmapPath,
  },
  reasons,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase18 gate report written: ${outPath}`)
process.exit(blocked ? 1 : 0)
NODE
