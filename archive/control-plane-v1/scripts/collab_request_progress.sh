#!/usr/bin/env bash
set -euo pipefail

# collab_request_progress.sh - Main requests progress update from worker
# Usage: ./control-plane/scripts/collab_request_progress.sh --assignment-ref ASSIGN_... [--notes "message"]

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

ASSIGNMENT_REF=""
NOTES=""
DRY_RUN=0

cd "${ROOT_DIR}"

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_request_progress.sh --assignment-ref ASSIGN_... [options]

Options:
  --assignment-ref <id>  Assignment to request progress on (must be acknowledged)
  --notes <text>         Optional context for the request
  --dry-run              Validate only, do not create message
  -h, --help             Show this message

Protocol:
  1. Main sends MSGK_PROGRESS_REQUEST to worker
  2. Worker receives request and must respond with:
     - PROGRESS_REPORT event (status update), or
     - Fulfillment (if work is complete)
  3. If no response within timeout, Main may escalate

Example:
  ./control-plane/scripts/collab_request_progress.sh \
    --assignment-ref ASSIGN_PHASE34_AY13_GEMINI_I02 \
    --notes "2 hours elapsed since acknowledge, checking status"
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --assignment-ref) ASSIGNMENT_REF="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${ASSIGNMENT_REF}" ]]; then
  echo "error: --assignment-ref is required" >&2
  exit 1
fi

# Resolve assignment details
_resolve="$(python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$ASSIGNMENT_REF" <<'PY'
import sys
import yaml
from pathlib import Path

doc = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
assignment_ref = sys.argv[2]

assignments = {a.get("id"): a for a in doc.get("assignments", [])}
assignment = assignments.get(assignment_ref)

if not assignment:
    raise SystemExit(f"unknown assignment: {assignment_ref}")

# Find associated message
messages = [m for m in doc.get("messages", []) if m.get("assignment_ref") == assignment_ref]
if not messages:
    raise SystemExit(f"no message found for assignment: {assignment_ref}")

msg = messages[0]

# Check if message is acknowledged
msg_events = [e for e in doc.get("message_events", []) if e.get("message_ref") == msg.get("id")]
msg_events.sort(key=lambda e: int(e.get("at_seq", 0)))
current_status = msg_events[-1].get("to_status") if msg_events else msg.get("initial_status")

if current_status != "acknowledged":
    raise SystemExit(f"message not acknowledged (status: {current_status}), cannot request progress")

print(assignment.get("agent_ref", ""))
print(assignment.get("worktree", ""))
print(msg.get("id", ""))
print(assignment.get("checkbox_ref", ""))
PY
)" || {
  echo "error: failed to resolve assignment" >&2
  exit 1
}

readarray -t _lines <<<"${_resolve}"
AGENT_REF="${_lines[0]}"
WORKTREE="${_lines[1]}"
MESSAGE_REF="${_lines[2]}"
CHECKBOX_REF="${_lines[3]}"

echo "Resolved:"
echo "  Assignment: ${ASSIGNMENT_REF}"
echo "  Checkbox: ${CHECKBOX_REF}"
echo "  Agent: ${AGENT_REF}"
echo "  Worktree: ${WORKTREE}"
echo "  Message: ${MESSAGE_REF}"

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "DRY RUN: would send progress request"
  exit 0
fi

# Create progress request message
NOW="$(date -u +%Y%m%dT%H%M%SZ)"
MSG_ID="MSG_PROGRESS_${CHECKBOX_REF}_${AGENT_REF}_${NOW}"

echo "Creating progress request: ${MSG_ID}"

python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$MSG_ID" "$AGENT_REF" "$WORKTREE" "$ASSIGNMENT_REF" "$MESSAGE_REF" "$NOTES" <<'PY'
import sys
import yaml
from pathlib import Path
from datetime import datetime, timezone

model_path = Path(sys.argv[1])
doc = yaml.safe_load(model_path.read_text(encoding="utf-8"))

msg_id = sys.argv[2]
agent_ref = sys.argv[3]
worktree = sys.argv[4]
assignment_ref = sys.argv[5]
orig_msg_ref = sys.argv[6]
notes = sys.argv[7]

# Add message
new_msg = {
    "id": msg_id,
    "kind_ref": "MSGK_PROGRESS_REQUEST",
    "assignment_ref": assignment_ref,
    "from_agent_ref": "AGENT_MAIN",
    "to_agent_ref": agent_ref,
    "from_worktree": "/home/andrey/src/cicsc",
    "to_worktree": worktree,
    "initial_status": "sent",
    "payload_refs": [],
    "evidence_refs": [],
    "evidence_bindings": [],
    "notes": notes or f"Progress request for {assignment_ref}",
}
doc["messages"].append(new_msg)

# Add sent event
seq = max([int(e.get("at_seq", 0)) for e in doc.get("message_events", [])] + [0]) + 1
event = {
    "id": f"MSGEV_{msg_id}_SENT_1",
    "message_ref": msg_id,
    "from_status": "",
    "to_status": "sent",
    "at_seq": seq,
    "timestamp": datetime.now(timezone.utc).isoformat(),
    "actor_agent_ref": "AGENT_MAIN",
    "evidence": [],
    "notes": "Progress request dispatched",
}
doc["message_events"].append(event)

model_path.write_text(yaml.dump(doc, sort_keys=False, allow_unicode=True), encoding="utf-8")
print(f"Created: {msg_id}")
PY

./control-plane/scripts/generate_views.sh >/dev/null

echo "Progress request sent to ${AGENT_REF}"
echo "Worker should respond with progress report or fulfillment"
