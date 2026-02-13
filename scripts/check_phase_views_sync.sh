#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const roadmap = fs.readFileSync(path.resolve('ROADMAP.md'), 'utf8').split(/\r?\n/)
const phaseSectionRe = /^## ([A-Z]{1,2})\. Phase (\d+):\s+/
const checkboxRe = /^- \[(x| )\] ([A-Z]{1,2})(\d)\.(\d)\s+/

let currentPhaseNo = null
const roadmapPhaseNums = new Set()
const roadmapMap = new Map() // key phase.m.i -> bool
for (const line of roadmap) {
  const p = line.match(phaseSectionRe)
  if (p) {
    currentPhaseNo = Number(p[2])
    roadmapPhaseNums.add(currentPhaseNo)
    continue
  }
  const c = line.match(checkboxRe)
  if (c && currentPhaseNo !== null) {
    const key = `${currentPhaseNo}.${c[3]}.${c[4]}`
    roadmapMap.set(key, c[1] === 'x')
  }
}

const phaseFiles = fs
  .readdirSync(process.cwd())
  .filter((f) => /^PHASE\d+\.md$/.test(f))
  .filter((f) => {
    const m = f.match(/^PHASE(\d+)\.md$/)
    return roadmapPhaseNums.has(Number(m[1]))
  })
const errors = []

for (const pf of phaseFiles) {
  const m = pf.match(/^PHASE(\d+)\.md$/)
  const phaseNo = Number(m[1])
  const txt = fs.readFileSync(path.resolve(pf), 'utf8')
  const lines = txt.split(/\r?\n/)
  const phaseMap = new Map()
  const re = /^- \[(x| )\] P(\d+)\.(\d)\.(\d)\s+/
  for (const line of lines) {
    const pm = line.match(re)
    if (!pm) continue
    const pnum = Number(pm[2])
    if (pnum !== phaseNo) {
      errors.push(`${pf}: checkbox phase prefix P${pnum} mismatches file phase ${phaseNo}`)
      continue
    }
    const key = `${pnum}.${pm[3]}.${pm[4]}`
    phaseMap.set(key, pm[1] === 'x')
  }

  for (const [k, v] of phaseMap.entries()) {
    if (!roadmapMap.has(k)) {
      errors.push(`${pf}: missing ${k} in ROADMAP.md`)
      continue
    }
    if (roadmapMap.get(k) !== v) {
      errors.push(`${pf}: status mismatch for ${k}`)
    }
  }

  for (const [k] of roadmapMap.entries()) {
    if (!k.startsWith(`${phaseNo}.`)) continue
    if (!phaseMap.has(k)) errors.push(`${pf}: missing roadmap checkbox ${k}`)
  }
}

if (errors.length > 0) {
  console.error('phase view sync check failed')
  for (const e of errors) console.error(`- ${e}`)
  process.exit(1)
}

console.log('phase view sync check passed')
NODE
