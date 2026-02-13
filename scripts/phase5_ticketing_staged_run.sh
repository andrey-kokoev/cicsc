#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase5-ticketing-staged-run.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase5-ticketing-staged-run.${name}.log"
  if "$@" >"${log_path}" 2>&1; then
    echo "\"${name}\":{\"status\":\"pass\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
  else
    echo "\"${name}\":{\"status\":\"fail\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
  fi
}

CHECKS=()
CHECKS+=("$(run_check invariants ./scripts/node_test.sh tests/oracle/replay-and-constraints.test.ts)")
CHECKS+=("$(run_check conformance_sqlite ./scripts/run_conformance_required.sh default)")
CHECKS+=("$(run_check migration_protocol ./scripts/node_test.sh tests/oracle/migration-preflight.test.ts tests/oracle/migration-dry-run.test.ts tests/oracle/cutover-protocol.test.ts tests/oracle/rollback-workflow.test.ts)")
CHECKS+=("$(run_check conformance_postgres ./scripts/run_cross_backend_gate.sh)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase5-ticketing-staged-run-v1\","
  echo "  \"vertical\": \"ticketing\","
  echo "  \"timestamp_unix\": $(date +%s),"
  echo "  \"overall\": \"${overall}\","
  echo "  \"checks\": {"
  for i in "${!CHECKS[@]}"; do
    suffix=","
    if [[ "$i" -eq "$((${#CHECKS[@]} - 1))" ]]; then suffix=""; fi
    echo "    ${CHECKS[$i]}${suffix}"
  done
  echo "  }"
  echo "}"
} > "${OUT_PATH}"

echo "staged run report written: ${OUT_PATH}"
