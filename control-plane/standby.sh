#!/usr/bin/env bash
#==============================================================================
# standby.sh - Agent polling loop
#
# Usage:
#   export AGENT_ID=AGENT_GEMINI
#   ./control-plane/standby.sh
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
if [[ -z "$AGENT_ID" ]]; then
    echo "ERROR: AGENT_ID not set. Run: export AGENT_ID=AGENT_xxx" >&2
    exit 1
fi

echo "=== Agent $AGENT_ID starting standby ==="
echo "Polls every 5 seconds. Set AGENT_ID env var."
echo ""

while true; do
    python3 -c "
import sys
import os
import time
sys.path.insert(0, 'control-plane')
from db import set_agent_status, get_agent_assignment

agent_id = os.environ.get('AGENT_ID')

assignment = get_agent_assignment(agent_id)
set_agent_status(agent_id, 'busy' if assignment else 'standing_by')

if assignment:
    print('')
    print('=' * 50)
    print(f'WORK ASSIGNED: {assignment[\"checkbox_ref\"]}')
    print(f'Task: {assignment.get(\"task_description\", \"No description\")}')
    print('=' * 50)
    print('')
    print('Do the work, then commit and push.')
    print('This script will keep polling.')
    print('')
else:
    sys.stdout.write(f'[{time.strftime(\"%H:%M:%S\")}] No work, polling...')
    sys.stdout.flush()
"
    
    sleep 5
done
