#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

LOG_DIR="${ROOT_DIR}/control-plane/logs/auto-dispatch-loop"
PID_FILE="${LOG_DIR}/auto-dispatch-loop.pid"
LOG_FILE="${LOG_DIR}/auto-dispatch-loop.log"

mkdir -p "${LOG_DIR}"

AGENT_REF="${AGENT_REF:-AGENT_KIMI}"
BATCH_SIZE="${BATCH_SIZE:-3}"
INTERVAL_SECONDS="${INTERVAL_SECONDS:-5}"
MAX_INFLIGHT="${MAX_INFLIGHT:-0}"
WAIT_TIMEOUT_SECONDS="${WAIT_TIMEOUT_SECONDS:-30}"
FRICTION_DECISION="${FRICTION_DECISION:-accept_later}"
FRICTION_BACKLOG_REF="${FRICTION_BACKLOG_REF:-phase36.collab-ergonomics}"

if [[ -f "${PID_FILE}" ]]; then
  existing_pid="$(cat "${PID_FILE}")"
  if [[ -n "${existing_pid}" ]] && ps -p "${existing_pid}" > /dev/null 2>&1; then
    echo "auto-dispatch-loop already running pid=${existing_pid}"
    exit 0
  fi
fi

cd "${ROOT_DIR}"
nohup ./control-plane/scripts/auto_dispatch_loop.sh \
  --agent-ref "${AGENT_REF}" \
  --batch-size "${BATCH_SIZE}" \
  --interval-seconds "${INTERVAL_SECONDS}" \
  --max-inflight "${MAX_INFLIGHT}" \
  --wait-timeout-seconds "${WAIT_TIMEOUT_SECONDS}" \
  --friction-decision "${FRICTION_DECISION}" \
  --friction-backlog-ref "${FRICTION_BACKLOG_REF}" \
  >> "${LOG_FILE}" 2>&1 &
new_pid="$!"
echo "${new_pid}" > "${PID_FILE}"
echo "auto-dispatch-loop launched pid=${new_pid} log=${LOG_FILE}"
