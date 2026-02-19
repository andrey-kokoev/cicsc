#!/usr/bin/env bash
#==============================================================================
# autoassign.sh - Mechanistic core: assigns open work to idle agents (LIFO)
#
# Usage:
#   ./autoassign.sh           # Run once
#   ./autoassign.sh --loop    # Run continuously
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

LOOP=0
if [[ "${1:-}" == "--loop" ]]; then
    LOOP=1
fi

assign_work() {
    python3 << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_idle_agents, get_open_checkboxes, get_assigned_checkboxes, assign_work_to_agent

idle_agents = get_idle_agents()
open_checkboxes = get_open_checkboxes()
already_assigned = get_assigned_checkboxes()

available_work = [cb for cb in open_checkboxes if cb["id"] not in already_assigned]

if not idle_agents:
    print("No idle agents")
    sys.exit(0)

if not available_work:
    print("No open work")
    sys.exit(0)

print(f"Idle agents: {len(idle_agents)}")
print(f"Open work: {len(available_work)}")

assigned_count = 0
for agent in idle_agents:
    if not available_work:
        break
    
    cb = available_work.pop()
    assign_work_to_agent(cb["id"], agent["id"])
    print(f"Assigned {cb['id']} -> {agent['id']}")
    assigned_count += 1

print(f"Total assigned: {assigned_count}")
PY
}

if [[ $LOOP -eq 1 ]]; then
    echo "=== Auto-assigner running in loop (LIFO) ==="
    while true; do
        assign_work
        sleep 10
    done
else
    assign_work
fi
