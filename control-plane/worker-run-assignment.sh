#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"
source "$SCRIPT_DIR/output.sh"

AGENT_ID=""
CHECKBOX=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --agent)
            AGENT_ID="${2:-}"
            shift 2
            ;;
        --checkbox)
            CHECKBOX="${2:-}"
            shift 2
            ;;
        --help|-h)
            echo "Usage: $0 --agent <AGENT_ID> --checkbox <CHECKBOX>"
            exit 0
            ;;
        *)
            echo "Unknown arg: $1" >&2
            exit 1
            ;;
    esac
done

if [[ -z "$AGENT_ID" || -z "$CHECKBOX" ]]; then
    echo "Usage: $0 --agent <AGENT_ID> --checkbox <CHECKBOX>" >&2
    exit 1
fi

append_event() {
    local event_type="$1"
    local details="${2:-}"
    python3 - "$event_type" "$AGENT_ID" "$CHECKBOX" "$details" <<'PY'
import sys
sys.path.insert(0, 'control-plane')
from db import append_event

event_type = sys.argv[1]
agent = sys.argv[2]
checkbox = sys.argv[3]
details = sys.argv[4] if len(sys.argv) > 4 and sys.argv[4] else None
append_event(event_type, checkbox_ref=checkbox, agent_ref=agent, details=details)
PY
}

block_and_fail() {
    local reason="$1"
    append_event "work_failed" "$reason"
    python3 - "$AGENT_ID" "$CHECKBOX" "$reason" <<'PY'
import sys
sys.path.insert(0, 'control-plane')
from db import block_agent

agent = sys.argv[1]
checkbox = sys.argv[2]
reason = sys.argv[3]
block_agent(agent, reason, checkbox_ref=checkbox)
PY
    emit_result error worker_run_assignment "blocked" "checkbox=$CHECKBOX" "reason=$reason"
    exit 10
}

if ! python3 - "$AGENT_ID" "$CHECKBOX" <<'PY'
import sys
sys.path.insert(0, 'control-plane')
from db import get_agent_assignment

agent = sys.argv[1]
checkbox = sys.argv[2]
assignment = get_agent_assignment(agent)
if not assignment or assignment.get('checkbox_ref') != checkbox:
    raise SystemExit(1)
PY
then
    block_and_fail "assignment_not_owned"
fi

append_event "work_started" "worker-run-assignment"

if ! python3 - "$AGENT_ID" "$CHECKBOX" <<'PY'
import sys
sys.path.insert(0, 'control-plane')
from db import touch_assignment_lease

agent = sys.argv[1]
checkbox = sys.argv[2]
if not touch_assignment_lease(agent, checkbox, lease_seconds=60):
    raise SystemExit(1)
PY
then
    block_and_fail "lease_refresh_failed"
fi

if [[ -x "$SCRIPT_DIR/agent-work.sh" ]]; then
    if ! "$SCRIPT_DIR/agent-work.sh" --agent "$AGENT_ID" --checkbox "$CHECKBOX"; then
        block_and_fail "implementation_hook_failed"
    fi
fi

if ! ./control-plane/check_gates.sh; then
    block_and_fail "gates_failed"
fi
append_event "gates_pass" "check_gates.sh"

BRANCH="$(git branch --show-current)"
if [[ -z "$BRANCH" || "$BRANCH" == "main" ]]; then
    block_and_fail "invalid_work_branch"
fi

if ! git log -1 --pretty=%s | grep -Eiq "(^|[^A-Za-z0-9])${CHECKBOX}([^A-Za-z0-9]|$)"; then
    block_and_fail "head_commit_missing_checkbox_ref"
fi

HEAD_SHA="$(git rev-parse --short HEAD)"

if ! git rev-parse --verify "origin/$BRANCH" >/dev/null 2>&1 || ! git merge-base --is-ancestor HEAD "origin/$BRANCH"; then
    if ! git push origin "$BRANCH"; then
        block_and_fail "push_failed"
    fi
fi
append_event "push_verified" "branch=$BRANCH commit=$HEAD_SHA"

integrate_rc=0
./control-plane/integrate.sh integrate "$CHECKBOX" --agent "$AGENT_ID" || integrate_rc=$?
if [[ $integrate_rc -ne 0 ]]; then
    if [[ $integrate_rc -eq 3 ]]; then
        block_and_fail "integrate_failed_owner_mismatch"
    fi
    block_and_fail "integrate_failed"
fi

append_event "worker_closed" "commit=$HEAD_SHA"
emit_result ok worker_run_assignment "assignment closed" "checkbox=$CHECKBOX" "commit=$HEAD_SHA"
