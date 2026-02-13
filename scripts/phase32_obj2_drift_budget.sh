#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase32-obj2-drift-budget.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase32-obj2-drift-budget.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check parity_continuity ./scripts/check_phase10_parity_continuity.sh)")
CHECKS+=("$(run_check category_model_conformance ./scripts/check_category_model_conformance.sh)")
CHECKS+=("$(run_check canonical_execution_model ./scripts/check_canonical_execution_model.sh)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

# Drift budget policy for this phase: no unresolved semantic regressions in required checks.
budget_max_failures=0
actual_failures=0
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    actual_failures=$((actual_failures + 1))
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase32-obj2-drift-budget-v1\","
  echo "  \"timestamp_unix\": $(date +%s),"
  echo "  \"overall\": \"${overall}\","
  echo "  \"objective\": \"OBJ2\","
  echo "  \"drift_budget\": {"
  echo "    \"max_failures\": ${budget_max_failures},"
  echo "    \"actual_failures\": ${actual_failures},"
  echo "    \"within_budget\": $([[ ${actual_failures} -le ${budget_max_failures} ]] && echo true || echo false)"
  echo "  },"
  echo "  \"checks\": {"
  for i in "${!CHECKS[@]}"; do
    suffix=","
    if [[ "$i" -eq "$((${#CHECKS[@]} - 1))" ]]; then suffix=""; fi
    echo "    ${CHECKS[$i]}${suffix}"
  done
  echo "  }"
  echo "}"
} > "${OUT_PATH}"

echo "phase32 obj2 drift budget report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
