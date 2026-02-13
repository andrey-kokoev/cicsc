#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase11-deferred-differentials.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase11-deferred-differentials.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check having_exec_vs_oracle ./scripts/node_test.sh tests/conformance/phase9-having-exec-vs-oracle.test.ts)")
CHECKS+=("$(run_check having_postgres_harness ./scripts/node_test.sh tests/conformance/phase10-postgres-having-harness.test.ts)")
CHECKS+=("$(run_check exists_feature_gate_negative ./scripts/node_test.sh tests/core/phase9-sql-feature-gates-negative.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

cat > "${OUT_PATH}" <<JSON
{
  "version": "cicsc/phase11-deferred-differentials-v1",
  "timestamp_unix": $(date +%s),
  "overall": "${overall}",
  "checks": {
    ${CHECKS[0]},
    ${CHECKS[1]},
    ${CHECKS[2]}
  }
}
JSON

echo "phase11 deferred differentials report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
