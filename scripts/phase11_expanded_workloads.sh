#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase11-expanded-workloads.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase11-expanded-workloads.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check reference_workloads ./scripts/node_test.sh tests/verticals/phase9-reference-workloads.test.ts)")
CHECKS+=("$(run_check parity_continuity ./scripts/node_test.sh tests/conformance/phase10-parity-continuity.test.ts)")
CHECKS+=("$(run_check migration_continuity ./scripts/node_test.sh tests/oracle/phase10-migration-continuity.test.ts)")
CHECKS+=("$(run_check operational_slo_continuity ./scripts/node_test.sh tests/oracle/phase10-operational-slo-continuity.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

cat > "${OUT_PATH}" <<JSON
{
  "version": "cicsc/phase11-expanded-workloads-v1",
  "timestamp_unix": $(date +%s),
  "overall": "${overall}",
  "checks": {
    ${CHECKS[0]},
    ${CHECKS[1]},
    ${CHECKS[2]},
    ${CHECKS[3]}
  }
}
JSON

echo "phase11 expanded workloads report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
