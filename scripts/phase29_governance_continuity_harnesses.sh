#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase29-governance-continuity-harnesses.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"
cd "${ROOT_DIR}"; mkdir -p "${OUT_DIR}"
run_check(){ local name="$1"; shift; local log_path="${OUT_DIR}/phase29-governance-continuity-harnesses.${name}.log"; local status; if "$@" >"${log_path}" 2>&1; then status="pass"; else status="fail"; fi; echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"; }
CHECKS=()
CHECKS+=("$(run_check phase29_baseline_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase29-baseline-continuity.json","utf8"));process.exit(j.status==="pass"?0:1)')")
CHECKS+=("$(run_check phase29_assurance_expansion_closure_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase29-assurance-expansion-closure-report.json","utf8"));process.exit(j.status==="pass"?0:1)')")
CHECKS+=("$(run_check phase29_gate_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase29-gate.json","utf8"));process.exit(j.blocked===false?0:1)')")
CHECKS+=("$(run_check runbook_operator_contract rg -q "^#|runbook|operator|incident" docs/pilot/runbook.md)")
overall="pass"; for kv in "${CHECKS[@]}"; do [[ "${kv}" == *"\"status\":\"fail\""* ]] && overall="fail"; done
cat > "${OUT_PATH}" <<JSON
{"version":"cicsc/phase29-governance-continuity-harnesses-v1","timestamp_unix":$(date +%s),"overall":"${overall}","checks":{${CHECKS[0]},${CHECKS[1]},${CHECKS[2]},${CHECKS[3]}}}
JSON
echo "phase29 governance-continuity harness report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
