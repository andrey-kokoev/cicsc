#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COLLAB_PATH="${ROOT_DIR}/control-plane/collaboration/collab-model.yaml"

ASSIGNMENT_REF=""
FROM_AGENT_REF="AGENT_MAIN"
MESSAGE_ID=""
EVENT_ID=""
INITIAL_STATUS="sent"
COMMIT_SHA=""
NOTES=""
NO_REFRESH=0
DRY_RUN=0
PAYLOAD_REFS=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_dispatch.sh \
    --assignment-ref ASSIGN_... \
    --payload-ref <path> [--payload-ref <path> ...] \
    [options]

Options:
  --from-agent-ref <id>  Dispatching agent (default: AGENT_MAIN).
  --message-id <id>      Optional explicit message id (default auto).
  --event-id <id>        Optional explicit initial event id (default auto).
  --initial-status <s>   Initial status: queued|sent (default: sent).
  --commit <sha>         Commit to bind on initial event (default: current HEAD short).
  --notes <text>         Optional message note.
  --no-refresh           Do not regenerate views after update.
  --dry-run              Validate and print summary, but do not write.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --assignment-ref) ASSIGNMENT_REF="${2:-}"; shift 2 ;;
    --payload-ref) PAYLOAD_REFS+=("${2:-}"); shift 2 ;;
    --from-agent-ref) FROM_AGENT_REF="${2:-}"; shift 2 ;;
    --message-id) MESSAGE_ID="${2:-}"; shift 2 ;;
    --event-id) EVENT_ID="${2:-}"; shift 2 ;;
    --initial-status) INITIAL_STATUS="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${ASSIGNMENT_REF}" ]]; then
  echo "--assignment-ref is required" >&2
  usage >&2
  exit 1
fi
if [[ ${#PAYLOAD_REFS[@]} -lt 1 ]]; then
  echo "at least one --payload-ref is required" >&2
  usage >&2
  exit 1
fi
if [[ "${INITIAL_STATUS}" != "queued" && "${INITIAL_STATUS}" != "sent" ]]; then
  echo "--initial-status must be queued or sent" >&2
  exit 1
fi

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

python3 - "$COLLAB_PATH" "$ASSIGNMENT_REF" "$FROM_AGENT_REF" "$MESSAGE_ID" "$EVENT_ID" "$INITIAL_STATUS" "$COMMIT_SHA" "$NOTES" "$DRY_RUN" "${PAYLOAD_REFS[@]}" <<'PY'
import re
import sys
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
assignment_ref = sys.argv[2]
from_agent_ref = sys.argv[3]
message_id_arg = sys.argv[4]
event_id_arg = sys.argv[5]
initial_status = sys.argv[6]
commit_sha = sys.argv[7]
notes_arg = sys.argv[8]
dry_run = sys.argv[9] == "1"
payload_refs = sys.argv[10:]

data = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
agents = {a.get("id"): a for a in data.get("agents", [])}
assignments = {a.get("id"): a for a in data.get("assignments", [])}
messages = data.get("messages", [])
events = data.get("message_events", [])
message_kinds = {m.get("id") for m in data.get("message_kinds", [])}
transition = data.get("message_transition_policy", {})
initial_statuses = set(transition.get("initial_statuses", []))
terminal_statuses = set(transition.get("terminal_statuses", []))
gov = data.get("worktree_governance", {})
dispatch_kind = gov.get("assignment_dispatch_kind_ref", "MSGK_ASSIGNMENT_DISPATCH")

if assignment_ref not in assignments:
    raise SystemExit(f"unknown assignment_ref: {assignment_ref}")
if from_agent_ref not in agents:
    raise SystemExit(f"unknown from_agent_ref: {from_agent_ref}")
if not re.fullmatch(r"[0-9a-f]{7,40}", commit_sha):
    raise SystemExit(f"invalid commit sha: {commit_sha}")
if dispatch_kind not in message_kinds:
    raise SystemExit(f"dispatch kind not declared in message_kinds: {dispatch_kind}")
if initial_status not in initial_statuses:
    raise SystemExit(f"initial status {initial_status} not allowed by transition policy")

assignment = assignments[assignment_ref]
to_agent_ref = assignment.get("agent_ref")
if to_agent_ref not in agents:
    raise SystemExit(f"assignment target agent missing: {to_agent_ref}")

existing = [m for m in messages if m.get("assignment_ref") == assignment_ref]
events_by_message = {}
for e in events:
    events_by_message.setdefault(e.get("message_ref"), []).append(e)

for m in existing:
    evs = sorted(events_by_message.get(m.get("id"), []), key=lambda e: int(e.get("at_seq", 0)))
    if not evs:
        continue
    current = evs[-1].get("to_status")
    if current not in terminal_statuses:
        raise SystemExit(
            f"assignment {assignment_ref} already has non-terminal message {m.get('id')} ({current})"
        )

if message_id_arg:
    message_id = message_id_arg
else:
    base = assignment_ref.removeprefix("ASSIGN_")
    candidate = f"MSG_{base}_DISPATCH"
    suffix = 1
    existing_ids = {m.get("id") for m in messages}
    while candidate in existing_ids:
        suffix += 1
        candidate = f"MSG_{base}_DISPATCH_{suffix}"
    message_id = candidate

if any(m.get("id") == message_id for m in messages):
    raise SystemExit(f"duplicate message id: {message_id}")

if event_id_arg:
    event_id = event_id_arg
else:
    base = message_id.removeprefix("MSG_")
    event_id = f"MSGEV_{base}_{initial_status.upper()}_1"

if any(e.get("id") == event_id for e in events):
    raise SystemExit(f"duplicate event id: {event_id}")

from_worktree = agents[from_agent_ref].get("worktree")
to_worktree = assignment.get("worktree")
branch = assignment.get("branch")

msg = {
    "id": message_id,
    "kind_ref": dispatch_kind,
    "assignment_ref": assignment_ref,
    "from_agent_ref": from_agent_ref,
    "to_agent_ref": to_agent_ref,
    "from_worktree": from_worktree,
    "to_worktree": to_worktree,
    "branch": branch,
    "initial_status": initial_status,
    "payload_refs": payload_refs,
    "evidence_refs": [],
    "evidence_bindings": [],
    "notes": notes_arg or f"Dispatch for {assignment_ref} via collab_dispatch.sh",
}

ev = {
    "id": event_id,
    "message_ref": message_id,
    "from_status": None,
    "to_status": initial_status,
    "actor_agent_ref": from_agent_ref,
    "at_seq": 1,
    "commit": commit_sha,
    "evidence_bindings": [],
    "notes": f"Initial dispatch event for {assignment_ref}.",
}

if dry_run:
    print("dry-run: validated dispatch payload")
    print(f"message_id={message_id}")
    print(f"event_id={event_id}")
    raise SystemExit(0)

messages.append(msg)
events.append(ev)
data["messages"] = messages
data["message_events"] = events

collab_path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
print(f"dispatched {assignment_ref} as {message_id}")
PY

if [[ "${DRY_RUN}" -eq 0 && "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

if [[ "${DRY_RUN}" -eq 0 ]]; then
  ./control-plane/scripts/collab_validate.sh >/dev/null
fi
