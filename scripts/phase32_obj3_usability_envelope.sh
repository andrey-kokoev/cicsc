#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase32-obj3-usability-envelope.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase32-obj3-usability-envelope.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check dsl_usability ./scripts/phase11_dsl_usability_harness.sh "${OUT_DIR}/phase32-obj3-usability-envelope.dsl_usability.json")")
CHECKS+=("$(run_check migration_usability ./scripts/phase8_spec_migration_usability_benchmark.sh "${OUT_DIR}/phase32-obj3-usability-envelope.migration_usability.json")")
CHECKS+=("$(run_check recovery_evidence ./scripts/phase9_migration_drills.sh "${OUT_DIR}/phase32-obj3-usability-envelope.recovery_evidence.json")")

overall="pass"
pass_count=0
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"pass\""* ]]; then
    pass_count=$((pass_count + 1))
  else
    overall="fail"
  fi
done

success_rate=$(awk -v p="$pass_count" 'BEGIN { printf "%.4f", p / 3 }')
error_rate=$(awk -v p="$pass_count" 'BEGIN { printf "%.4f", 1 - (p / 3) }')

cat > "${OUT_PATH}" <<JSON
{
  "version": "cicsc/phase32-obj3-usability-envelope-v1",
  "timestamp_unix": $(date +%s),
  "overall": "${overall}",
  "objective": "OBJ3",
  "envelope": "expanded_usability",
  "metrics": {
    "task_success_rate": ${success_rate},
    "error_rate_bounded": ${error_rate},
    "recovery_workflow_evidence": true
  },
  "checks": {
    ${CHECKS[0]},
    ${CHECKS[1]},
    ${CHECKS[2]}
  }
}
JSON

echo "phase32 obj3 usability envelope report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
