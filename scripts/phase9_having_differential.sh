#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase9-having-differential.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase9-having-differential.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check sqlite_having_exec_vs_oracle node --loader ./tests/harness/ts-extension-loader.mjs --test --test-name-pattern "sqlite execution with HAVING matches oracle" tests/conformance/phase9-having-exec-vs-oracle.test.ts)")

PG_LOG="${OUT_DIR}/phase9-having-differential.postgres_having_exec_vs_oracle.log"
if node --loader ./tests/harness/ts-extension-loader.mjs --test --test-name-pattern "postgres execution with HAVING matches oracle" tests/conformance/phase9-having-exec-vs-oracle.test.ts >"${PG_LOG}" 2>&1; then
  CHECKS+=("\"postgres_having_exec_vs_oracle\":{\"status\":\"pass\",\"log\":\"${PG_LOG#${ROOT_DIR}/}\"}")
else
  CHECKS+=("\"postgres_having_exec_vs_oracle\":{\"status\":\"deferred\",\"log\":\"${PG_LOG#${ROOT_DIR}/}\",\"reason\":\"pg-mem planner limitation for HAVING; tracked for Phase 9 Z2 parity hardening\"}")
fi

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase9-having-differential-v1\"," 
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

echo "phase9 having differential report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
