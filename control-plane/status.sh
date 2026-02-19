#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

MODE=""
AGENT_ID=""
JSON_MODE=0

set_mode() {
    local next="$1"
    if [[ -n "$MODE" && "$MODE" != "$next" ]]; then
        echo "ERROR: --agent, --all, and --summary are mutually exclusive" >&2
        exit 1
    fi
    MODE="$next"
}

usage() {
    cat <<USAGE
Usage:
  $0 --agent <AGENT_ID> [--json]
  $0 --all [--json]
  $0 --summary [--json]
USAGE
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --agent)
            AGENT_ID="${2:-}"
            set_mode "agent"
            shift 2
            ;;
        --all)
            set_mode "all"
            shift
            ;;
        --summary)
            set_mode "summary"
            shift
            ;;
        --json)
            JSON_MODE=1
            shift
            ;;
        --help|-h)
            usage
            exit 0
            ;;
        *)
            echo "Unknown arg: $1" >&2
            usage >&2
            exit 1
            ;;
    esac
done

if [[ -z "$MODE" ]]; then
    usage >&2
    exit 1
fi

if [[ "$MODE" == "agent" && -z "$AGENT_ID" ]]; then
    echo "ERROR: --agent requires an agent id" >&2
    usage >&2
    exit 1
fi

python3 - "$MODE" "$AGENT_ID" "$JSON_MODE" <<'PY'
import json
import sys
sys.path.insert(0, 'control-plane')
from db import get_agent_snapshot, list_agent_snapshots, get_collab_summary

mode = sys.argv[1]
agent_id = sys.argv[2]
json_mode = bool(int(sys.argv[3]))

if mode == "agent":
    payload = get_agent_snapshot(agent_id)
elif mode == "all":
    payload = list_agent_snapshots()
elif mode == "summary":
    payload = get_collab_summary()
else:
    print(f"unknown mode: {mode}", file=sys.stderr)
    raise SystemExit(2)

if json_mode:
    print(json.dumps(payload, indent=2, sort_keys=True))
    raise SystemExit(0)

if mode == "agent":
    snapshot = payload
    print(f"Agent: {snapshot.get('agent_id')}")
    print(f"Exists: {snapshot.get('exists')}")
    print(f"State: {snapshot.get('status')}")
    print(f"PID: {snapshot.get('pid')}")
    print(f"Heartbeat age (s): {snapshot.get('heartbeat_age_seconds')}")
    print(f"Lease age (s): {snapshot.get('lease_age_seconds')}")
    print(f"Lease expires in (s): {snapshot.get('lease_expires_in_seconds')}")
    print(f"Blocked reason: {snapshot.get('blocked_reason')}")

    assignment = snapshot.get('assignment')
    if assignment:
        print(f"Assignment: {assignment.get('checkbox_ref')}")
        print(f"Task: {assignment.get('task_description')}")
        print(f"Lease token: {assignment.get('lease_token')}")
        print(f"Lease expires at: {assignment.get('lease_expires_at')}")
    else:
        print("Assignment: none")

    last_event = snapshot.get('last_event')
    if last_event:
        print(f"Last event: {last_event.get('event_type')} @ {last_event.get('timestamp')}")
    else:
        print("Last event: none")
elif mode == "all":
    snapshots = payload
    print(f"Agents: {len(snapshots)}")
    for snapshot in snapshots:
        assignment = snapshot.get('assignment') or {}
        checkbox = assignment.get('checkbox_ref') or "none"
        print(
            f"- {snapshot.get('agent_id')}: state={snapshot.get('status')} "
            f"assignment={checkbox} heartbeat_age_s={snapshot.get('heartbeat_age_seconds')} "
            f"lease_expires_in_s={snapshot.get('lease_expires_in_seconds')}"
        )
elif mode == "summary":
    summary = payload
    print(f"Generated at: {summary.get('generated_at')}")
    print(f"Total agents: {summary.get('total_agents')}")
    print(
        "Agents by state: "
        f"standing_by={summary.get('standing_by')} busy={summary.get('busy')} blocked={summary.get('blocked')} "
        f"assignable_idle={summary.get('assignable_idle_count')}"
    )
    print(
        "Work: "
        f"assigned={summary.get('assigned_count')} open={summary.get('open_count')} "
        f"unassigned_open={summary.get('unassigned_open_count')} stale_lease={summary.get('stale_lease_count')}"
    )
PY
