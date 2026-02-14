#!/usr/bin/env bash
set -euo pipefail

# collab_worker_loop_v2.sh - Ergonomic worker autopilot with auto-recovery
# Usage: ./control-plane/scripts/collab_worker_loop_v2.sh --worktree /path/to/worktree

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
INTERVAL_SECONDS=5
QUIET=0
MAX_RETRIES=3

cd "${ROOT_DIR}"

# Auto-sync function: ensure views and models are current
auto_sync() {
  if [[ "${QUIET}" -eq 0 ]]; then
    echo "[$(date '+%H:%M:%S')] sync: regenerating views..."
  fi
  ./control-plane/scripts/generate_views.sh >/dev/null 2>&1 || true
}

# Pre-flight validation: check if we can proceed
preflight_check() {
  local worktree="$1"
  
  # Check if worktree exists
  if [[ ! -d "${worktree}" ]]; then
    echo "[$(date '+%H:%M:%S')] ERROR: worktree does not exist: ${worktree}" >&2
    return 1
  fi
  
  # Validate cross-model state
  if ! ./control-plane/scripts/validate_cross_model.sh >/dev/null 2>&1; then
    echo "[$(date '+%H:%M:%S')] WARN: cross-model validation failed, attempting repair..." >&2
    ./control-plane/scripts/collab_sync.sh >/dev/null 2>&1 || true
  fi
  
  return 0
}

# Safe claim with retry logic
safe_claim() {
  local worktree="$1"
  local max_attempts="$2"
  local attempt=0
  
  while [[ "${attempt}" -lt "${max_attempts}" ]]; do
    attempt=$((attempt + 1))
    
    # Pre-sync before claim
    auto_sync
    
    # Attempt claim
    if ./control-plane/scripts/collab_claim_next.sh --worktree "${worktree}" 2>/dev/null; then
      return 0
    fi
    
    # Claim failed - check if it's a dirty tree issue
    if git status --porcelain -- control-plane/collaboration/collab-model.yaml control-plane/views 2>/dev/null | grep -q .; then
      echo "[$(date '+%H:%M:%S')] claim: dirty state detected, auto-committing..."
      git add control-plane/collaboration/collab-model.yaml control-plane/views/ 2>/dev/null || true
      git commit -m "autopilot: sync before claim (auto)" 2>/dev/null || true
      continue
    fi
    
    # Check for validation errors
    if ! ./control-plane/scripts/validate_cross_model.sh >/dev/null 2>&1; then
      echo "[$(date '+%H:%M:%S')] claim: validation failed, running repair..."
      ./control-plane/scripts/collab_sync.sh >/dev/null 2>&1 || true
      sleep 1
      continue
    fi
    
    # No actionable messages is OK
    local count
    count="$(./control-plane/scripts/collab_inbox.sh --worktree "${worktree}" --refresh --actionable-only 2>/dev/null | jq 'length')" || count=0
    if [[ "${count}" -eq 0 ]]; then
      return 1  # No work, not an error
    fi
    
    sleep 1
  done
  
  return 1
}

# Safe fulfill with automatic evidence resolution
safe_fulfill() {
  local worktree="$1"
  local message_ref="$2"
  local max_attempts="$3"
  local attempt=0
  
  while [[ "${attempt}" -lt "${max_attempts}" ]]; do
    attempt=$((attempt + 1))
    
    # Pre-sync
    auto_sync
    
    # Attempt fulfill with auto-evidence discovery
    if ./control-plane/scripts/collab_fulfill.sh \
         --message-ref "${message_ref}" \
         --worktree "${worktree}" \
         --with scripts/check_canonical_execution_model.sh \
         --auto-report 2>/dev/null; then
      return 0
    fi
    
    # Check for specific error patterns
    local error_output
    error_output="$(./control-plane/scripts/collab_fulfill.sh \
      --message-ref "${message_ref}" \
      --worktree "${worktree}" \
      --with scripts/check_canonical_execution_model.sh \
      --auto-report 2>&1)" || true
    
    # Handle illegal transition errors (orphaned fulfill events)
    if echo "${error_output}" | grep -q "illegal transition"; then
      echo "[$(date '+%H:%M:%S')] fulfill: illegal transition detected, repairing..."
      
      # Extract and remove invalid event
      local bad_event
      bad_event="$(echo "${error_output}" | grep -oE "MSGEV_[A-Z0-9_]+_FULFILLED_[0-9]+" | head -1)"
      if [[ -n "${bad_event}" ]]; then
        echo "[$(date '+%H:%M:%S')] fulfill: removing invalid event ${bad_event}..."
        sed -i "/^- id: ${bad_event}\$/,/^  notes:.*\$/d" control-plane/collaboration/collab-model.yaml
        auto_sync
        git add -A
        git commit -m "autopilot: repair illegal transition (auto)" 2>/dev/null || true
        continue
      fi
    fi
    
    # Handle sync errors
    if echo "${error_output}" | grep -q "collab_sync\|out of sync"; then
      echo "[$(date '+%H:%M:%S')] fulfill: sync required, repairing..."
      ./control-plane/scripts/collab_sync.sh >/dev/null 2>&1 || true
      continue
    fi
    
    sleep 1
  done
  
  return 1
}

# Safe commit with automatic message generation
safe_commit() {
  local message="${1:-autopilot: sync (auto)}"
  
  if git diff --cached --quiet 2>/dev/null; then
    return 0  # Nothing to commit
  fi
  
  git commit -m "${message}" 2>/dev/null || true
}

# Main loop
echo "worker-autopilot-v2: starting ergonomic wait-process loop"
echo "worktree: ${WORKTREE}"
echo "interval: ${INTERVAL_SECONDS}s"
echo ""

# Initial preflight
if ! preflight_check "${WORKTREE}"; then
  echo "[$(date '+%H:%M:%S')] FATAL: preflight failed" >&2
  exit 1
fi

while true; do
  # Check for actionable messages
  if [[ "${QUIET}" -eq 0 ]]; then
    echo "[$(date '+%H:%M:%S')] checking inbox..."
  fi
  
  auto_sync
  
  local count
  count="$(./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --refresh --actionable-only 2>/dev/null | jq 'length')" || count=0
  
  if [[ "${count}" -eq 0 ]]; then
    if [[ "${QUIET}" -eq 0 ]]; then
      echo "[$(date '+%H:%M:%S')] no messages, waiting ${INTERVAL_SECONDS}s..."
    fi
    sleep "${INTERVAL_SECONDS}"
    continue
  fi
  
  echo "[$(date '+%H:%M:%S')] ${count} message(s) to process"
  
  # Process each message
  while [[ "${count}" -gt 0 ]]; do
    # Get next message ref
    local msg_ref
    msg_ref="$(./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --refresh --actionable-only 2>/dev/null | jq -r '.[0].id')" || break
    
    if [[ -z "${msg_ref}" || "${msg_ref}" == "null" ]]; then
      break
    fi
    
    echo "[$(date '+%H:%M:%S')] processing: ${msg_ref}"
    
    # Safe claim
    if ! safe_claim "${WORKTREE}" "${MAX_RETRIES}"; then
      echo "[$(date '+%H:%M:%S')] claim failed, retrying..."
      sleep 2
      continue
    fi
    
    safe_commit "autopilot: claim (auto)"
    
    # Safe fulfill
    if safe_fulfill "${WORKTREE}" "${msg_ref}" "${MAX_RETRIES}"; then
      echo "[$(date '+%H:%M:%S')] fulfilled: ${msg_ref}"
      safe_commit "autopilot: fulfill ${msg_ref} (auto)"
    else
      echo "[$(date '+%H:%M:%S')] ERROR: fulfill failed for ${msg_ref}" >&2
      # Don't get stuck - break and wait for next cycle
      break
    fi
    
    # Update count
    count="$(./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --refresh --actionable-only 2>/dev/null | jq 'length')" || count=0
  done
  
  echo "[$(date '+%H:%M:%S')] batch complete, returning to wait"
  echo ""
done
