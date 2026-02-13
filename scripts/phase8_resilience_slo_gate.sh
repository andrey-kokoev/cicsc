#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase8-resilience-slo.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase8-resilience-slo.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check verify_path ./scripts/node_test.sh tests/oracle/verify-streaming.test.ts tests/oracle/replay-and-constraints.test.ts)")
CHECKS+=("$(run_check migrate_path ./scripts/phase7_check_migration_protocol.sh)")
CHECKS+=("$(run_check command_path ./scripts/node_test.sh tests/runtime/execute-command-tx-seq.test.ts tests/runtime/execute-command-tx-idempotency.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase8-resilience-slo-v1\","
  echo "  \"timestamp_unix\": $(date +%s),"
  echo "  \"overall\": \"${overall}\","
  echo "  \"slo_targets\": {"
  echo "    \"verify_path_success_rate\": \">= 99.5%\","
  echo "    \"migrate_path_success_rate\": \">= 99%\","
  echo "    \"command_path_success_rate\": \">= 99.5%\""
  echo "  },"
  echo "  \"error_budget\": {"
  echo "    \"verify_path_failures_per_window\": 0,"
  echo "    \"migrate_path_failures_per_window\": 0,"
  echo "    \"command_path_failures_per_window\": 0"
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

echo "phase8 resilience slo report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
