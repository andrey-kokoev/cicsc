#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

PID_FILE="${ROOT_DIR}/control-plane/logs/auto-dispatch-loop/auto-dispatch-loop.pid"

if [[ ! -f "${PID_FILE}" ]]; then
  echo "auto-dispatch-loop not running (no pid file)"
  exit 0
fi

pid="$(cat "${PID_FILE}")"
if [[ -n "${pid}" ]] && ps -p "${pid}" > /dev/null 2>&1; then
  kill "${pid}"
  echo "auto-dispatch-loop stopped pid=${pid}"
else
  echo "auto-dispatch-loop not running (stale pid=${pid})"
fi
rm -f "${PID_FILE}"
