#!/usr/bin/env bash
set -euo pipefail

# collab_worker_loop.sh - Robust worker loop with circuit breaker and auto-repair
# Usage: ./control-plane/scripts/collab_worker_loop.sh --worktree /path/to/worktree

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
INTERVAL_SECONDS=5
MAX_CONSECUTIVE_FAILURES=5
FAILURE_WINDOW_SECONDS=300  # 5 minutes

# State tracking
CONSECUTIVE_FAILURES=0
FIRST_FAILURE_TIME=""
LAST_SUCCESS_TIME="$(date +%s)"
TOTAL_PROCESSED=0

cd "${ROOT_DIR}"

log() {
  echo "[$(date '+%H:%M:%S')] $*"
}

# Circuit breaker check
check_circuit_breaker() {
  if [[ "${CONSECUTIVE_FAILURES}" -ge "${MAX_CONSECUTIVE_FAILURES}" ]]; then
    local now
    now="$(date +%s)"
    local elapsed=$((now - FIRST_FAILURE_TIME))
    
    log "CIRCUIT BREAKER TRIPPED"
    log "  Consecutive failures: ${CONSECUTIVE_FAILURES}"
    log "  Time in failure state: ${elapsed}s"
    log "  Total processed before failure: ${TOTAL_PROCESSED}"
    log ""
    log "Manual intervention required. Common issues:"
    log "  1. Run: ./control-plane/scripts/collab_sync.sh"
    log "  2. Check: ./control-plane/scripts/validate_cross_model.sh"
    log "  3. Review: git status"
    log ""
    log "After fixing, restart this script."
    
    return 1
  fi
  return 0
}

# Record failure
record_failure() {
  local error_msg="${1:-unknown}"
  
  CONSECUTIVE_FAILURES=$((CONSECUTIVE_FAILURES + 1))
  
  if [[ -z "${FIRST_FAILURE_TIME}" ]]; then
    FIRST_FAILURE_TIME="$(date +%s)"
  fi
  
  log "FAILURE #${CONSECUTIVE_FAILURES}: ${error_msg}"
}

# Record success
record_success() {
  CONSECUTIVE_FAILURES=0
  FIRST_FAILURE_TIME=""
  LAST_SUCCESS_TIME="$(date +%s)"
  TOTAL_PROCESSED=$((TOTAL_PROCESSED + 1))
}

# Process one message with full error handling
process_one() {
  local worktree="$1"
  
  # Get next message
  local msg_ref
  msg_ref="$(./control-plane/scripts/collab_inbox.sh --worktree "${worktree}" --refresh --actionable-only 2>/dev/null | jq -r '.[0].id')" || {
    record_failure "inbox query failed"
    return 1
  }
  
  if [[ -z "${msg_ref}" || "${msg_ref}" == "null" ]]; then
    # No messages is not a failure
    return 2  # Special code: no work
  fi
  
  log "processing: ${msg_ref}"
  
  # Use atomic execute
  if ./control-plane/scripts/collab_execute.sh --worktree "${worktree}" --message-ref "${msg_ref}" 2>/dev/null; then
    log "completed: ${msg_ref}"
    record_success
    return 0
  else
    record_failure "execute failed for ${msg_ref}"
    return 1
  fi
}

# Main loop
log "worker-loop: starting robust loop (worktree: ${WORKTREE})"
log "  Circuit breaker: ${MAX_CONSECUTIVE_FAILURES} failures"
log "  Interval: ${INTERVAL_SECONDS}s"
log "  Press Ctrl+C to stop"
log ""

while true; do
  # Check circuit breaker first
  if ! check_circuit_breaker; then
    exit 1
  fi
  
  # Try to process one message
  process_one "${WORKTREE}"
  process_result=$?
  
  if [[ "${process_result}" -eq 2 ]]; then
    # No messages available - this is normal, not failure
    if [[ "${CONSECUTIVE_FAILURES}" -gt 0 ]]; then
      log "recovered: no more failures, waiting for new work"
      CONSECUTIVE_FAILURES=0
      FIRST_FAILURE_TIME=""
    fi
    
    log "waiting ${INTERVAL_SECONDS}s for new messages... (processed: ${TOTAL_PROCESSED})"
    sleep "${INTERVAL_SECONDS}"
    
  elif [[ "${process_result}" -eq 0 ]]; then
    # Success - immediately check for more work
    continue
    
  else
    # Failure recorded by process_one, wait briefly before retry
    sleep 2
  fi
done
