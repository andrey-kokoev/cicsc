#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase9-sql-negative-coverage.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

LOG_PATH="${OUT_DIR}/phase9-sql-negative-coverage.typecheck_negative.log"
if ./scripts/node_test.sh tests/core/phase9-sql-feature-gates-negative.test.ts tests/core/phase9-sql-unsupported-negative.test.ts >"${LOG_PATH}" 2>&1; then
  status="pass"
else
  status="fail"
fi

cat > "${OUT_PATH}" <<JSON
{
  "version": "cicsc/phase9-sql-negative-coverage-v1",
  "timestamp_unix": $(date +%s),
  "overall": "${status}",
  "checks": {
    "typecheck_negative": {
      "status": "${status}",
      "log": "${LOG_PATH#${ROOT_DIR}/}"
    }
  }
}
JSON

echo "phase9 sql negative coverage report written: ${OUT_PATH}"
[[ "${status}" == "pass" ]]
