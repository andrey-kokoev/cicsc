#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const errors = []

const read = (p) => fs.readFileSync(path.resolve(p), 'utf8')
const exists = (p) => fs.existsSync(path.resolve(p))

const objective = read('control-plane/objectives/objective-model.yaml')
const capability = read('control-plane/capabilities/capability-model.yaml')
const execution = read('control-plane/execution/execution-ledger.yaml')
const gate = read('control-plane/gates/gate-model.yaml')

const objectiveIds = new Set([...objective.matchAll(/^\s*-\s+id:\s+(OBJ\d+)\s*$/gm)].map((m) => m[1]))
if (objectiveIds.size === 0) errors.push('objective-model: no OBJ ids found')

for (const m of capability.matchAll(/objective_refs:\s*\[([^\]]*)\]/g)) {
  const refs = m[1].split(',').map((s) => s.trim()).filter(Boolean)
  for (const ref of refs) {
    if (!objectiveIds.has(ref)) errors.push(`capability-model: unknown objective ref ${ref}`)
  }
}

for (const m of objective.matchAll(/\n\s*ref:\s*([^\n]+)\n/g)) {
  const ref = m[1].trim()
  if (!exists(ref)) errors.push(`objective-model: missing referenced artifact ${ref}`)
}
for (const m of capability.matchAll(/\n\s*ref:\s*([^\n]+)\n/g)) {
  const ref = m[1].trim()
  if (!exists(ref)) errors.push(`capability-model: missing referenced artifact ${ref}`)
}

const phaseMatches = [...execution.matchAll(/^\s*-\s+id:\s+([A-Z]{1,2})\s*\n\s*number:\s*(\d+)\s*\n\s*title:\s*([^\n]+)\n\s*status:\s*(\w+)\s*$/gm)]
if (phaseMatches.length === 0) errors.push('execution-ledger: no phases found')

const seenIds = new Set()
const seenNumbers = new Set()
let last = -1
for (const m of phaseMatches) {
  const id = m[1]
  const number = Number(m[2])
  if (seenIds.has(id)) errors.push(`execution-ledger: duplicate phase id ${id}`)
  if (seenNumbers.has(number)) errors.push(`execution-ledger: duplicate phase number ${number}`)
  if (number <= last) errors.push(`execution-ledger: phase numbers not strictly increasing at ${id}`)
  seenIds.add(id)
  seenNumbers.add(number)
  last = number
}

for (const m of gate.matchAll(/^\s*-\s+(scripts\/[^\s]+)\s*$/gm)) {
  const ref = m[1]
  if (!exists(ref)) errors.push(`gate-model: missing required script ${ref}`)
}

if (errors.length) {
  console.error('cross-model validation failed')
  for (const e of errors) console.error(`- ${e}`)
  process.exit(1)
}

console.log('cross-model validation passed')
NODE
