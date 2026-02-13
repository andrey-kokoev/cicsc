#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase30-objective-closure-run.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase30-objective-closure-run.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check spec_to_ir_compile ./scripts/node_test.sh tests/spec/reference-vertical-usability.test.ts tests/verticals/kanban-spec.test.ts)")
CHECKS+=("$(run_check sqlite_exec_vs_oracle ./scripts/node_test.sh tests/conformance/sqlite-exec-vs-oracle-smoke.test.ts)")
CHECKS+=("$(run_check postgres_exec_vs_oracle ./scripts/node_test.sh tests/conformance/postgres-exec-vs-oracle.test.ts)")
CHECKS+=("$(run_check migration_replay_verify ./scripts/node_test.sh tests/conformance/migration-replay-conformance.test.ts tests/oracle/migration-preflight.test.ts tests/oracle/migration-dry-run.test.ts tests/oracle/cutover-protocol.test.ts tests/oracle/rollback-workflow.test.ts)")
CHECKS+=("$(run_check concurrency_replay ./scripts/node_test.sh tests/concurrency/causality-replay.test.ts tests/concurrency/transaction-model.test.ts tests/oracle/replay-determinism-multistream.test.ts)")
CHECKS+=("$(run_check dsl_usability ./scripts/node_test.sh tests/spec/reference-vertical-usability.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

cat > "${OUT_PATH}" <<JSON
{
  "version": "cicsc/phase30-objective-closure-run-v1",
  "timestamp_unix": $(date +%s),
  "overall": "${overall}",
  "checks": {
    ${CHECKS[0]},
    ${CHECKS[1]},
    ${CHECKS[2]},
    ${CHECKS[3]},
    ${CHECKS[4]},
    ${CHECKS[5]}
  }
}
JSON

echo "phase30 objective closure run written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
