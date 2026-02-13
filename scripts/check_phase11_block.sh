#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase11-gate.json}"
cd "${ROOT_DIR}"

STATUS_TMP="$(mktemp)"
trap 'rm -f "${STATUS_TMP}"' EXIT
./control-plane/scripts/export_execution_status.py control-plane/execution/execution-ledger.yaml > "${STATUS_TMP}"

node - "${OUT_PATH}" "${STATUS_TMP}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const executionStatusFile = process.argv[3]
const phaseNo = 11
const checklistPath = 'docs/pilot/phase10-exit-checklist.json'
const executionStatusPath = 'control-plane/views/execution-status.generated.json'

const checklist = JSON.parse(fs.readFileSync(path.resolve(checklistPath), 'utf8'))
const executionStatus = JSON.parse(fs.readFileSync(path.resolve(executionStatusFile), 'utf8'))

const rows = (executionStatus.rows ?? []).filter((r) => Number(r.phase_number) === phaseNo)
const checklistPass = (checklist.items ?? []).every((i) => i.status === 'pass')
const allChecked = rows.length > 0 && rows.every((r) => r.status === 'done')

const code = rows[0]?.checkbox_id?.match(/^([A-Z]{1,2})\d+\.\d+$/)?.[1]?.toLowerCase() ?? 'phase'
const blocked = !(checklistPass && allChecked)
const reasons = []
if (!checklistPass) reasons.push('phase10_exit_checklist_not_pass')
if (!allChecked) reasons.push(`phase_${code}_series_incomplete`)

const report = {
  version: 'cicsc/phase11-gate-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  blocked,
  basis: {
    checklist: checklistPath,
    execution_status: executionStatusPath,
  },
  reasons,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}
`, 'utf8')
console.log(`phase${phaseNo} gate report written: ${outPath}`)
process.exit(blocked ? 1 : 0)
NODE
