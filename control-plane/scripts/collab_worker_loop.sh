#!/usr/bin/env bash
set -euo pipefail

# collab_worker_loop.sh - Simple robust worker wait-process loop
# Usage: ./control-plane/scripts/collab_worker_loop.sh --worktree /path/to/worktree

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
INTERVAL_SECONDS=5
QUIET=0

cd "${ROOT_DIR}"

echo "worker-loop: starting (worktree: ${WORKTREE})"
echo "Press Ctrl+C to stop"
echo ""

while true; do
  # Process all current messages
  while true; do
    # Refresh and check
    ./control-plane/scripts/generate_views.sh >/dev/null 2>&1 || true
    
    local count
    count="$(./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --refresh --actionable-only 2>/dev/null | jq 'length')" || count=0
    
    if [[ "${count}" -eq 0 ]]; then
      break
    fi
    
    echo "[$(date '+%H:%M:%S')] ${count} message(s) - processing..."
    
    # Process one batch (claim + fulfill + commit)
    if ./control-plane/scripts/collab_run_once.sh --worktree "${WORKTREE}" 2>/dev/null; then
      echo "[$(date '+%H:%M:%S')] completed one assignment"
    else
      echo "[$(date '+%H:%M:%S')] processing failed, attempting repair..."
      
      # Common repairs
      ./control-plane/scripts/collab_sync.sh >/dev/null 2>&1 || true
      
      # If still failing, skip and continue
      sleep 2
    fi
    
    # Commit any pending changes
    if ! git diff --cached --quiet 2>/dev/null; then
      git commit -m "autopilot: sync ($(date '+%H%M'))" 2>/dev/null || true
    fi
  done
  
  # Wait for new messages
  if [[ "${QUIET}" -eq 0 ]]; then
    echo "[$(date '+%H:%M:%S')] waiting ${INTERVAL_SECONDS}s for new messages..."
  fi
  sleep "${INTERVAL_SECONDS}"
done
