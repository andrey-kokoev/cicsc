#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase7-concurrency-adversarial.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

run_check () {
  local name="$1"
  shift
  local log_path="${OUT_DIR}/phase7-concurrency-adversarial.${name}.log"
  local status
  if "$@" >"${log_path}" 2>&1; then
    status="pass"
  else
    status="fail"
  fi
  echo "\"${name}\":{\"status\":\"${status}\",\"log\":\"${log_path#${ROOT_DIR}/}\"}"
}

CHECKS=()
CHECKS+=("$(run_check phase7_multitenant_replay ./scripts/node_test.sh tests/concurrency/phase7-adversarial-multitenant-replay.test.ts)")
CHECKS+=("$(run_check causality_replay ./scripts/node_test.sh tests/concurrency/causality-replay.test.ts)")
CHECKS+=("$(run_check replay_multistream ./scripts/node_test.sh tests/oracle/replay-determinism-multistream.test.ts)")
CHECKS+=("$(run_check transaction_model ./scripts/node_test.sh tests/concurrency/transaction-model.test.ts)")

overall="pass"
for kv in "${CHECKS[@]}"; do
  if [[ "${kv}" == *"\"status\":\"fail\""* ]]; then
    overall="fail"
    break
  fi
done

{
  echo "{"
  echo "  \"version\": \"cicsc/phase7-concurrency-adversarial-v1\","
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

echo "phase7 concurrency adversarial report written: ${OUT_PATH}"
[[ "${overall}" == "pass" ]]
