#!/usr/bin/env bash
set -euo pipefail

# collab_worker_loop.sh - Ergonomic continuous worker loop with auto-recovery
# Usage: ./control-plane/scripts/collab_worker_loop.sh --worktree /path/to/worktree

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
INTERVAL_SECONDS=5

cd "${ROOT_DIR}"

echo "worker-loop: starting continuous loop (worktree: ${WORKTREE})"
echo "Press Ctrl+C to stop"
echo ""

repair_and_continue() {
  echo "[$(date '+%H:%M:%S')] attempting repair..."
  
  # Fix common issues
  ./control-plane/scripts/collab_sync.sh >/dev/null 2>&1 || true
  
  # Commit any pending changes
  if ! git diff --cached --quiet 2>/dev/null; then
    git commit -m "autopilot: sync ($(date +%H%M))" 2>/dev/null || true
  fi
  
  sleep 1
}

process_batch() {
  local worktree="$1"
  local processed=0
  
  while true; do
    # Check for messages
    local count
    count="$(./control-plane/scripts/collab_inbox.sh --worktree "${worktree}" --refresh --actionable-only 2>/dev/null | jq 'length')" || count=0
    
    if [[ "${count}" -eq 0 ]]; then
      break
    fi
    
    # Get first message
    local msg_ref
    msg_ref="$(./control-plane/scripts/collab_inbox.sh --worktree "${worktree}" --refresh --actionable-only 2>/dev/null | jq -r '.[0].id')" || break
    
    echo "[$(date '+%H:%M:%S')] claiming: ${msg_ref}"
    
    # Try to claim
    if ! ./control-plane/scripts/collab_claim_next.sh --worktree "${worktree}" --auto-commit 2>/dev/null; then
      echo "[$(date '+%H:%M:%S')] claim failed, repairing..."
      repair_and_continue
      continue
    fi
    
    echo "[$(date '+%H:%M:%S')] fulfilling: ${msg_ref}"
    
    # Try to fulfill
    if ./control-plane/scripts/collab_fulfill.sh \
         --message-ref "${msg_ref}" \
         --worktree "${worktree}" \
         --with scripts/check_canonical_execution_model.sh \
         --auto-report \
         --auto-commit 2>/dev/null; then
      echo "[$(date '+%H:%M:%S')] completed: ${msg_ref}"
      processed=$((processed + 1))
    else
      echo "[$(date '+%H:%M:%S')] fulfill failed, repairing..."
      repair_and_continue
    fi
  done
  
  return "${processed}"
}

# Main loop
while true; do
  # Process current batch
  process_batch "${WORKTREE}"
  
  # Wait for new work
  echo "[$(date '+%H:%M:%S')] waiting ${INTERVAL_SECONDS}s..."
  sleep "${INTERVAL_SECONDS}"
  echo ""
done
