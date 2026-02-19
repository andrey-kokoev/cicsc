#!/usr/bin/env bash
#==============================================================================
# autoassign.sh - Mechanistic core: assigns open work to standing_by agents
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

STATE_DIR="$ROOT/state"
LOCK_FILE="$STATE_DIR/autoassign.lock"
LOCK_DIR_FALLBACK="$STATE_DIR/autoassign.lock.d"
PID_FILE="$STATE_DIR/autoassign.pid"

acquire_single_instance_lock() {
    mkdir -p "$STATE_DIR"

    if command -v flock >/dev/null 2>&1; then
        exec 9>"$LOCK_FILE"
        if ! flock -n 9; then
            echo "Auto-assigner already running; exiting."
            exit 0
        fi
        echo $$ > "$PID_FILE"
        trap 'rm -f "$PID_FILE"' EXIT
        return
    fi

    if ! mkdir "$LOCK_DIR_FALLBACK" 2>/dev/null; then
        echo "Auto-assigner already running; exiting."
        exit 0
    fi
    echo $$ > "$PID_FILE"
    trap 'rm -f "$PID_FILE"; rmdir "$LOCK_DIR_FALLBACK" 2>/dev/null || true' EXIT
}

assign_work() {
    python3 << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import (
    get_assignable_agents,
    get_open_checkboxes,
    get_assigned_checkboxes,
    assign_work_to_agent,
    reclaim_stale_assignments,
    get_collab_summary,
)

reclaimed = reclaim_stale_assignments(heartbeat_grace_seconds=30)
if reclaimed:
    print(f"Reclaimed stale assignments: {len(reclaimed)}")
    for row in reclaimed:
        print(f"  Reclaimed {row['checkbox_ref']} from {row['agent_ref']}")

idle_agents = get_assignable_agents(max_heartbeat_age_seconds=30)
open_checkboxes = get_open_checkboxes()
already_assigned = get_assigned_checkboxes()
summary = get_collab_summary()

available_work = [cb for cb in open_checkboxes if cb["id"] not in already_assigned]

print(
    f"Status: idle_agents={summary['assignable_idle_count']} "
    f"open_checkboxes={summary['open_count']} "
    f"unassigned_open_work={summary['unassigned_open_count']} "
    f"stale_lease={summary['stale_lease_count']}"
)

if not idle_agents:
    print("No idle agents")
    sys.exit(0)

if not available_work:
    print("No open work")
    sys.exit(0)

assigned_count = 0
for agent in idle_agents:
    if not available_work:
        break

    cb = available_work.pop()
    if assign_work_to_agent(cb["id"], agent["id"], lease_seconds=60):
        print(f"Assigned {cb['id']} -> {agent['id']}")
        assigned_count += 1
    else:
        print(f"Skipped {cb['id']} for {agent['id']} (claim failed)")

print(f"Total assigned: {assigned_count}")
PY
}

if [[ $LOOP -eq 1 ]]; then
    acquire_single_instance_lock
    echo "=== Auto-assigner running in loop (LIFO) ==="
    echo "PID: $$"
    while true; do
        echo "--- $(date -u +"%Y-%m-%dT%H:%M:%SZ") ---"
        assign_work
        sleep 10
    done
else
    assign_work
fi
