#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase28-doc-consistency.json}"
cd "${ROOT_DIR}"

STATUS_TMP="$(mktemp)"
trap 'rm -f "${STATUS_TMP}"' EXIT
./control-plane/scripts/export_execution_status.py control-plane/execution/execution-ledger.yaml > "${STATUS_TMP}"

node - "${OUT_PATH}" "${STATUS_TMP}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const executionStatusFile = process.argv[3]
const phaseNo = 28
const phasePath = `PHASE${phaseNo}.md`
const phase = fs.readFileSync(path.resolve(phasePath), 'utf8')
const executionStatusPath = 'control-plane/views/execution-status.generated.json'
const executionStatus = JSON.parse(fs.readFileSync(path.resolve(executionStatusFile), 'utf8'))

function parsePhaseStatuses(md, n) {
  const out = new Map()
  const re = new RegExp(`^- \\[(x| )\\] P${n}\\.(\\d+)\\.(\\d+)\\s+`, 'gm')
  let m
  while ((m = re.exec(md)) !== null) {
    out.set(`${n}.${m[2]}.${m[3]}`, m[1] === 'x')
  }
  return out
}

function parseLedgerStatuses(statusRows, n) {
  const out = new Map()
  for (const row of statusRows ?? []) {
    if (Number(row.phase_number) !== n) continue
    const cm = String(row.checkbox_id ?? '').match(/^[A-Z]{1,2}(\d+)\.(\d+)$/)
    if (!cm) continue
    out.set(`${n}.${cm[1]}.${cm[2]}`, row.status === 'done')
  }
  return out
}

const phaseMap = parsePhaseStatuses(phase, phaseNo)
const ledgerMap = parseLedgerStatuses(executionStatus.rows, phaseNo)
const mismatches = []

for (const [id, checked] of phaseMap.entries()) {
  if (!ledgerMap.has(id)) {
    mismatches.push({ id, reason: 'missing_in_execution_ledger' })
    continue
  }
  if (ledgerMap.get(id) !== checked) {
    mismatches.push({ id, reason: 'status_mismatch' })
  }
}

for (const [id] of ledgerMap.entries()) {
  if (!phaseMap.has(id)) {
    mismatches.push({ id, reason: `missing_in_phase${phaseNo}` })
  }
}

const hasUnchecked = [...ledgerMap.values()].some((v) => !v)
const checklistPath = `docs/pilot/phase${phaseNo}-exit-checklist.json`
if (fs.existsSync(path.resolve(checklistPath))) {
  const checklist = JSON.parse(fs.readFileSync(path.resolve(checklistPath), 'utf8'))
  const governanceId = `P${phaseNo}_EXIT_GOVERNANCE_DRIFT`
  const governance = checklist.items?.find((i) => i.id === governanceId)
  if (governance?.status === 'pass' && hasUnchecked) {
    mismatches.push({
      id: governanceId,
      reason: `invalid_pass_while_phase${phaseNo}_series_unchecked`,
    })
  }
}

const report = {
  version: 'cicsc/phase28-doc-consistency-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  status: mismatches.length === 0 ? 'pass' : 'fail',
  basis: {
    phase: phasePath,
    execution_status: executionStatusPath,
  },
  checked_ids: [...ledgerMap.keys()].sort(),
  has_unchecked: hasUnchecked,
  mismatches,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}
`, 'utf8')
if (mismatches.length === 0) {
  console.log(`phase${phaseNo} docs consistency check passed`)
  process.exit(0)
}
console.error(`phase${phaseNo} docs consistency check failed`)
for (const m of mismatches) console.error(`- ${m.id}: ${m.reason}`)
process.exit(1)
NODE
