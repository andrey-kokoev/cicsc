#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase15-deployment-discipline-harnesses.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase15-deployment-discipline-harnesses.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check runbook_operator_contract node -e 'const fs=require("node:fs");const rb=fs.readFileSync("docs/pilot/runbook.md","utf8");const oc=fs.readFileSync("docs/pilot/operator-commands.md","utf8");const ok=rb.includes("## 2. Upgrade")&&rb.includes("## 3. Rollback")&&rb.includes("## 4. Verify Loop")&&oc.includes("## Cutover Flow")&&oc.includes("## Mandatory Artifacts");process.exit(ok?0:1)')")
CHECKS+=("$(run_check phase15_baseline_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase15-baseline-continuity.json","utf8"));process.exit(j.overall==="pass"?0:1)')")
CHECKS+=("$(run_check objective_required_gates_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase15-objective-required-gates.json","utf8"));process.exit(j.overall==="pass"?0:1)')")
CHECKS+=("$(run_check phase15_gate_status node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase15-gate.json","utf8"));process.exit(j.blocked===false?0:1)')")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

cat > "${OUT_PATH}" <<JSON
{
  "version": "cicsc/phase15-deployment-discipline-harnesses-v1",
  "timestamp_unix": $(date +%s),
  "overall": "${overall}",
  "checks": {
    ${CHECKS[0]},
    ${CHECKS[1]},
    ${CHECKS[2]},
    ${CHECKS[3]}
  }
}
JSON

echo "phase15 deployment discipline report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
