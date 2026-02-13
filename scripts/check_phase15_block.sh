#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase15-gate.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const checklistPath = 'docs/pilot/phase14-exit-checklist.json'
const roadmapPath = 'ROADMAP.md'

const checklist = JSON.parse(fs.readFileSync(path.resolve(checklistPath), 'utf8'))
const roadmap = fs.readFileSync(path.resolve(roadmapPath), 'utf8')

const checklistPass = (checklist.items ?? []).every((i) => i.status === 'pass')
const aeMatches = [...roadmap.matchAll(/^- \[(x| )\] AE(\d)\.(\d)\s+/gm)]
const allAeChecked = aeMatches.length > 0 && aeMatches.every((m) => m[1] === 'x')

const blocked = !(checklistPass && allAeChecked)
const reasons = []
if (!checklistPass) reasons.push('phase14_exit_checklist_not_pass')
if (!allAeChecked) reasons.push('roadmap_ae_series_incomplete')

const report = {
  version: 'cicsc/phase15-gate-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  blocked,
  basis: {
    checklist: checklistPath,
    roadmap: roadmapPath,
  },
  reasons,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
console.log(`phase15 gate report written: ${outPath}`)
process.exit(blocked ? 1 : 0)
NODE
