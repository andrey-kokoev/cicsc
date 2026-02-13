#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase13-doc-consistency.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const phase = fs.readFileSync(path.resolve('PHASE13.md'), 'utf8')
const roadmap = fs.readFileSync(path.resolve('ROADMAP.md'), 'utf8')
const checklist = JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase13-exit-checklist.json'), 'utf8'))

function parsePhaseStatuses(md) {
  const out = new Map()
  const re = /^- \[(x| )\] P13\.(\d)\.(\d)\s+/gm
  let m
  while ((m = re.exec(md)) !== null) out.set(`AD${m[2]}.${m[3]}`, m[1] === 'x')
  return out
}

function parseRoadmapStatuses(md) {
  const out = new Map()
  const re = /^- \[(x| )\] AD(\d)\.(\d)\s+/gm
  let m
  while ((m = re.exec(md)) !== null) out.set(`AD${m[2]}.${m[3]}`, m[1] === 'x')
  return out
}

const phaseMap = parsePhaseStatuses(phase)
const roadmapMap = parseRoadmapStatuses(roadmap)
const mismatches = []

for (const [id, checked] of phaseMap.entries()) {
  if (!roadmapMap.has(id)) mismatches.push({ id, reason: 'missing_in_roadmap' })
  else if (roadmapMap.get(id) !== checked) mismatches.push({ id, reason: 'status_mismatch' })
}
for (const [id] of roadmapMap.entries()) {
  if (!phaseMap.has(id)) mismatches.push({ id, reason: 'missing_in_phase13' })
}

const hasUnchecked = [...roadmapMap.values()].some((v) => !v)
const governance = (checklist.items ?? []).find((i) => i.id === 'P13_EXIT_GOVERNANCE')
if (governance?.status === 'pass' && hasUnchecked) {
  mismatches.push({ id: 'P13_EXIT_GOVERNANCE', reason: 'invalid_pass_while_ad_series_unchecked' })
}

const report = {
  version: 'cicsc/phase13-doc-consistency-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  status: mismatches.length === 0 ? 'pass' : 'fail',
  mismatches,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8')
if (mismatches.length === 0) {
  console.log('phase13 docs consistency check passed')
  process.exit(0)
}
console.error('phase13 docs consistency check failed')
process.exit(1)
NODE
