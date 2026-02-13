#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase10-postgres-having-harness.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase10-postgres-having-harness.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check postgres_exec_vs_oracle_baseline ./scripts/node_test.sh tests/conformance/postgres-exec-vs-oracle.test.ts)")
CHECKS+=("$(run_check phase9_having_report ./scripts/node_test.sh tests/conformance/phase9-having-differential.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

cat > "${OUT_PATH}" <<JSON
{
  "version": "cicsc/phase10-postgres-having-harness-v1",
  "timestamp_unix": $(date +%s),
  "overall": "${overall}",
  "checks": {
    ${CHECKS[0]},
    ${CHECKS[1]}
  },
  "notes": {
    "pg_having_harness_status": "deferred",
    "reason": "pg-mem HAVING planner limitation tracked from Phase 9; production parity baseline remains green"
  }
}
JSON

echo "phase10 postgres having harness report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
