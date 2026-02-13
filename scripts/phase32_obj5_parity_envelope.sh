#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase32-obj5-parity-envelope.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase32-obj5-parity-envelope.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check phase9_edgecase ./scripts/phase9_edgecase_parity.sh "${OUT_DIR}/phase32-obj5-parity-envelope.phase9_edgecase.json")")
CHECKS+=("$(run_check phase10_postgres ./scripts/phase10_postgres_having_harness.sh "${OUT_DIR}/phase32-obj5-parity-envelope.phase10_postgres.json")")
CHECKS+=("$(run_check phase12_multi_domain ./scripts/phase12_multi_domain_workloads.sh "${OUT_DIR}/phase32-obj5-parity-envelope.phase12_multi_domain.json")")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase32-obj5-parity-envelope-v1\","
  echo "  \"timestamp_unix\": $(date +%s),"
  echo "  \"overall\": \"${overall}\","
  echo "  \"objective\": \"OBJ5\","
  echo "  \"envelope\": \"expanded_parity\","
  echo "  \"checks\": {"
  for i in "${!CHECKS[@]}"; do
    suffix=","
    if [[ "$i" -eq "$((${#CHECKS[@]} - 1))" ]]; then suffix=""; fi
    echo "    ${CHECKS[$i]}${suffix}"
  done
  echo "  }"
  echo "}"
} > "${OUT_PATH}"

echo "phase32 obj5 parity envelope report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
