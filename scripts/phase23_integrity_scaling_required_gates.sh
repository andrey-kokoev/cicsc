#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase23-integrity-scaling-required-gates.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"
cd "${ROOT_DIR}"; mkdir -p "${OUT_DIR}"
run_check(){ local name="$1"; shift; local log_path="${OUT_DIR}/phase23-integrity-scaling-required-gates.${name}.log"; local status; if "$@" >"${log_path}" 2>&1; then status="pass"; else status="fail"; fi; echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"; }
CHECKS=()
CHECKS+=("$(run_check phase22_doc_consistency_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase22-doc-consistency.json","utf8"));process.exit(j.status==="pass"?0:1)')")
CHECKS+=("$(run_check phase22_resilience_expansion_required_gates_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase22-resilience-expansion-required-gates.json","utf8"));process.exit(j.overall==="pass"?0:1)')")
CHECKS+=("$(run_check phase23_baseline_continuity_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase23-baseline-continuity.json","utf8"));process.exit(j.overall==="pass"?0:1)')")
overall="pass"; for kv in "${CHECKS[@]}"; do [[ "${kv}" == *"\"status\":\"fail\""* ]] && overall="fail"; done
cat > "${OUT_PATH}" <<JSON
{"version":"cicsc/phase23-integrity-scaling-required-gates-v1","timestamp_unix":$(date +%s),"overall":"${overall}","checks":{${CHECKS[0]},${CHECKS[1]},${CHECKS[2]}}}
JSON
echo "phase23 integrity-scaling required gates report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
