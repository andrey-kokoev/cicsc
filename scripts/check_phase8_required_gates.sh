#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase8-required-gates.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase8-required-gates.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check equivalence bash -lc './scripts/phase8_large_cardinality_differential.sh && ./scripts/phase8_edgecase_parity.sh')")
CHECKS+=("$(run_check resilience ./scripts/phase8_resilience_slo_gate.sh)")
CHECKS+=("$(run_check ergonomics_safety ./scripts/node_test.sh tests/spec/phase8-dsl-ergonomics-negative.test.ts tests/spec/phase8-migration-authoring-assistant.test.ts tests/spec/phase8-spec-migration-usability-benchmark.test.ts tests/spec/phase8-ergonomics-report.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase8-required-gates-v1\"," 
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

echo "phase8 required gates report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
