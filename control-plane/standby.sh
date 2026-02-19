#!/usr/bin/env bash
#==============================================================================
# standby.sh - Agent polling loop
#
# Usage:
#   export AGENT_ID=AGENT_GEMINI
#   ./control-plane/standby.sh
#   ./control-plane/standby.sh --once-on-change
#
# Continuously polls for assigned work and outputs when found.
# When work is detected, outputs it and returns to polling.
# The external agent process handles actual work completion.
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

AGENT_ID="${AGENT_ID:-}"
ONCE_ON_CHANGE=0
if [[ "${1:-}" == "--once-on-change" ]]; then
    ONCE_ON_CHANGE=1
elif [[ -n "${1:-}" ]]; then
    echo "Usage: $0 [--once-on-change]" >&2
    exit 1
fi

if [[ -z "$AGENT_ID" ]]; then
    echo "ERROR: AGENT_ID not set. Run: export AGENT_ID=AGENT_xxx" >&2
    exit 1
fi

echo "=== Agent $AGENT_ID starting standby ==="
echo "Polls every 5 seconds. Set AGENT_ID env var."
if [[ "$ONCE_ON_CHANGE" -eq 1 ]]; then
    echo "Mode: once-on-change"
fi
echo ""

LAST_STATE=""
LAST_REF=""

while true; do
    POLL_OUT="$(
python3 - << 'PY'
import os
import sys
sys.path.insert(0, 'control-plane')
from db import set_agent_status, get_agent_assignment

agent_id = os.environ.get('AGENT_ID')
assignment = get_agent_assignment(agent_id)
set_agent_status(agent_id, 'busy' if assignment else 'standing_by')

if assignment:
    ref = str(assignment.get('checkbox_ref', ''))
    desc = str(assignment.get('task_description', 'No description'))
    print(f"assigned\t{ref}\t{desc}")
else:
    print("idle")
PY
)"

    IFS=$'\t' read -r STATE REF DESC <<< "$POLL_OUT"
    if [[ "$STATE" == "assigned" ]]; then
        SHOULD_PRINT=1
        if [[ "$ONCE_ON_CHANGE" -eq 1 && "$LAST_STATE" == "assigned" && "$LAST_REF" == "$REF" ]]; then
            SHOULD_PRINT=0
        fi
        if [[ "$SHOULD_PRINT" -eq 1 ]]; then
            echo ""
            echo "=================================================="
            echo "WORK ASSIGNED: $REF"
            echo "Task: ${DESC:-No description}"
            echo "=================================================="
            echo ""
            echo "Do the work, then commit and push."
            echo "This script will keep polling."
            echo ""
        fi
        LAST_STATE="assigned"
        LAST_REF="$REF"
    else
        SHOULD_PRINT=1
        if [[ "$ONCE_ON_CHANGE" -eq 1 && "$LAST_STATE" == "idle" ]]; then
            SHOULD_PRINT=0
        fi
        if [[ "$SHOULD_PRINT" -eq 1 ]]; then
            echo "[$(date +%H:%M:%S)] No work, polling..."
        fi
        LAST_STATE="idle"
        LAST_REF=""
    fi
    
    sleep 5
done
