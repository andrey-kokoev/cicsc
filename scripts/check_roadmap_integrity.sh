#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const md = fs.readFileSync(path.resolve('ROADMAP.md'), 'utf8')
const lines = md.split(/\r?\n/)

const phaseRe = /^## ([A-Z]{1,2})\. Phase (\d+):\s+/
const milestoneRe = /^### ([A-Z]{1,2})(\d)\./
const checkboxRe = /^- \[(x| )\] ([A-Z]{1,2})(\d)\.(\d)\s+/

let currentPhaseCode = null
let currentPhaseNo = null
let currentMilestone = null
let seenAnyPhase = false
let prevPhaseNo = null
let prevMilestoneNum = null
const milestoneCheckboxCount = new Map()

const errors = []

for (const line of lines) {
  const pm = line.match(phaseRe)
  if (pm) {
    seenAnyPhase = true
    currentPhaseCode = pm[1]
    currentPhaseNo = Number(pm[2])
    currentMilestone = null
    prevMilestoneNum = null
    if (prevPhaseNo !== null && currentPhaseNo !== prevPhaseNo + 1) {
      errors.push(`phase numbering not linear: got Phase ${currentPhaseNo} after Phase ${prevPhaseNo}`)
    }
    prevPhaseNo = currentPhaseNo
    continue
  }
  if (!seenAnyPhase) continue

  const mm = line.match(milestoneRe)
  if (mm) {
    const code = mm[1]
    const milestoneNum = Number(mm[2])
    if (code !== currentPhaseCode) {
      errors.push(`milestone ${mm[0]} not in current phase code ${currentPhaseCode}`)
    }
    if (prevMilestoneNum !== null && milestoneNum < prevMilestoneNum) {
      errors.push(`milestone order regressed in ${currentPhaseCode}: ${milestoneNum} after ${prevMilestoneNum}`)
    }
    prevMilestoneNum = milestoneNum
    currentMilestone = `${code}${milestoneNum}`
    milestoneCheckboxCount.set(currentMilestone, 0)
    continue
  }

  const cm = line.match(checkboxRe)
  if (cm) {
    const code = cm[2]
    const milestoneNum = Number(cm[3])
    const itemNum = Number(cm[4])
    if (!currentMilestone) {
      errors.push(`checkbox outside milestone: ${line}`)
      continue
    }
    const expectedMilestone = `${code}${milestoneNum}`
    if (code !== currentPhaseCode) {
      errors.push(`checkbox ${code}${milestoneNum}.${itemNum} not in phase ${currentPhaseCode}`)
    }
    if (expectedMilestone !== currentMilestone) {
      errors.push(`checkbox ${code}${milestoneNum}.${itemNum} not under milestone ${currentMilestone}`)
    }
    milestoneCheckboxCount.set(currentMilestone, (milestoneCheckboxCount.get(currentMilestone) ?? 0) + 1)
  }
}

for (const [m, n] of milestoneCheckboxCount.entries()) {
  if (n === 0) errors.push(`milestone ${m} has zero checkboxes`)
}

if (errors.length > 0) {
  console.error('roadmap integrity check failed')
  for (const e of errors) console.error(`- ${e}`)
  process.exit(1)
}

console.log('roadmap integrity check passed')
NODE
