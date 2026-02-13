#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase6-concurrency-conformance.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  local threshold_ms="$2"
  shift
  shift
  local log_path="${OUT_DIR}/phase6-concurrency-conformance.${name}.log"
  local t0 t1 duration status
  t0=$(date +%s%3N)
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  t1=$(date +%s%3N)
  duration=$((t1 - t0))
  if [[ "${status}" == "pass" && "${duration}" -gt "${threshold_ms}" ]]; then
    status="fail"
    echo "SLO breach: ${name} duration=${duration}ms threshold=${threshold_ms}ms" >> "${log_path}"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"duration_ms\":${duration},\"threshold_ms\":${threshold_ms},\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check causality_replay 8000 ./scripts/node_test.sh tests/concurrency/causality-replay.test.ts)")
CHECKS+=("$(run_check transaction_model 10000 ./scripts/node_test.sh tests/concurrency/transaction-model.test.ts)")
CHECKS+=("$(run_check replay_multistream 6000 ./scripts/node_test.sh tests/oracle/replay-determinism-multistream.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

total_duration=0
for kv in "${CHECKS[@]}"; do
  d="$(echo "${kv}" | sed -n 's/.*\"duration_ms\":\([0-9]\+\).*/\1/p')"
  if [[ -n "${d}" ]]; then
    total_duration=$((total_duration + d))
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase6-concurrency-conformance-v1\","
  echo "  \"timestamp_unix\": $(date +%s),"
  echo "  \"overall\": \"${overall}\","
  echo "  \"checks\": {"
  for i in "${!CHECKS[@]}"; do
    suffix=","
    if [[ "$i" -eq "$((${#CHECKS[@]} - 1))" ]]; then suffix=""; fi
    echo "    ${CHECKS[$i]}${suffix}"
  done
  echo "  },"
  echo "  \"metrics\": {"
  echo "    \"total_duration_ms\": ${total_duration}"
  echo "  }"
  echo "}"
} > "${OUT_PATH}"

echo "phase6 concurrency conformance report written: ${OUT_PATH}"
