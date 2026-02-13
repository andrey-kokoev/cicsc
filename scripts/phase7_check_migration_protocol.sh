#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase7-migration-protocol-check.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

LOG_PATH="${OUT_DIR}/phase7-migration-protocol-check.log"
if ./scripts/node_test.sh \
  tests/oracle/migration-preflight.test.ts \
  tests/oracle/migration-dry-run.test.ts \
  tests/oracle/cutover-protocol.test.ts \
  tests/oracle/rollback-workflow.test.ts \
  tests/oracle/migration-concurrency-drill.test.ts >"${LOG_PATH}" 2>&1; then
  status="pass"
else
  status="fail"
fi

{
  echo "{"
  echo "  \"version\": \"cicsc/phase7-migration-protocol-check-v1\","
  echo "  \"timestamp_unix\": $(date +%s),"
  echo "  \"overall\": \"${status}\","
  echo "  \"log\": \"${LOG_PATH#${ROOT_DIR}/}\""
  echo "}"
} > "${OUT_PATH}"

echo "phase7 migration protocol check written: ${OUT_PATH}"
[[ "${status}" == "pass" ]]
