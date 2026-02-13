#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase7-parity-differential.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase7-parity-differential.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check sqlite_scope_matrix ./scripts/node_test.sh tests/conformance/sqlite-lowering-vs-oracle.test.ts tests/conformance/sqlite-exec-vs-oracle-smoke.test.ts tests/conformance/sqlite-random-vs-oracle.test.ts)")
CHECKS+=("$(run_check postgres_scope_matrix ./scripts/node_test.sh tests/conformance/postgres-exec-matrix.test.ts tests/conformance/postgres-exec-vs-oracle.test.ts tests/conformance/postgres-constraint-matrix.test.ts)")
CHECKS+=("$(run_check cross_backend_diff ./scripts/node_test.sh tests/conformance/cross-backend-differential.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase7-parity-differential-v1\","
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

echo "phase7 parity differential report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
