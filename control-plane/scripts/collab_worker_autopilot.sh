#!/usr/bin/env bash
set -euo pipefail

# Worker Autopilot - Single command for continuous wait-process loop
# Usage: ./control-plane/scripts/collab_worker_autopilot.sh --worktree /path/to/worktree

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
INTERVAL_SECONDS=5
QUIET=0

cd "${ROOT_DIR}"

echo "worker-autopilot: starting continuous wait-process loop"
echo "worktree: ${WORKTREE}"
echo "interval: ${INTERVAL_SECONDS}s"
echo ""

while true; do
  # Wait for actionable messages
  if [[ "${QUIET}" -eq 0 ]]; then
    echo "[$(date '+%H:%M:%S')] waiting for messages..."
  fi
  
  # Poll inbox until messages found
  while true; do
    count="$(./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --refresh --actionable-only 2>/dev/null | jq 'length')"
    if [[ "${count}" -gt 0 ]]; then
      echo "[$(date '+%H:%M:%S')] ${count} actionable message(s) found"
      break
    fi
    sleep "${INTERVAL_SECONDS}"
  done
  
  # Process all actionable messages
  echo "[$(date '+%H:%M:%S')] processing..."
  ./control-plane/scripts/collab_process_messages.sh --role worker --worktree "${WORKTREE}" --max-iterations 50
  
  echo "[$(date '+%H:%M:%S')] batch complete, returning to wait"
  echo ""
done
