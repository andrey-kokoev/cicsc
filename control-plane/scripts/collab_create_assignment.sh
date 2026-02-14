#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COLLAB_PATH="${ROOT_DIR}/control-plane/collaboration/collab-model.yaml"

ASSIGNMENT_ID=""
AGENT_REF=""
CHECKBOX_REF=""
CLAIM_KIND_REF="CLAIM_EXECUTION_GOVERNANCE"
BRANCH=""
FROM_AGENT_REF="AGENT_MAIN"
MESSAGE_ID=""
EVENT_ID=""
INITIAL_STATUS="sent"
COMMIT_SHA=""
ASSIGNMENT_NOTES=""
DISPATCH_NOTES=""
NO_REFRESH=0
DRY_RUN=0
PAYLOAD_REFS=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_create_assignment.sh \
    --assignment-id ASSIGN_... \
    --agent-ref AGENT_... \
    --checkbox-ref AY1.2 \
    --branch phase34.ay1.2 \
    --payload-ref <path> [--payload-ref <path> ...] \
    [options]

Options:
  --claim-kind-ref <id>   Claim kind (default: CLAIM_EXECUTION_GOVERNANCE).
  --from-agent-ref <id>   Dispatching agent (default: AGENT_MAIN).
  --message-id <id>       Optional explicit message id (default: MSG_<assignment-without-ASSIGN_>_DISPATCH).
  --event-id <id>         Optional explicit initial event id.
  --initial-status <s>    Initial status: queued|sent (default: sent).
  --commit <sha>          Commit to bind on initial event (default: current HEAD short).
  --assignment-notes <t>  Assignment notes.
  --dispatch-notes <t>    Dispatch message notes.
  --no-refresh            Do not regenerate views after update.
  --dry-run               Validate and print created ids without writing.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --assignment-id) ASSIGNMENT_ID="${2:-}"; shift 2 ;;
    --agent-ref) AGENT_REF="${2:-}"; shift 2 ;;
    --checkbox-ref) CHECKBOX_REF="${2:-}"; shift 2 ;;
    --claim-kind-ref) CLAIM_KIND_REF="${2:-}"; shift 2 ;;
    --branch) BRANCH="${2:-}"; shift 2 ;;
    --payload-ref) PAYLOAD_REFS+=("${2:-}"); shift 2 ;;
    --from-agent-ref) FROM_AGENT_REF="${2:-}"; shift 2 ;;
    --message-id) MESSAGE_ID="${2:-}"; shift 2 ;;
    --event-id) EVENT_ID="${2:-}"; shift 2 ;;
    --initial-status) INITIAL_STATUS="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --assignment-notes) ASSIGNMENT_NOTES="${2:-}"; shift 2 ;;
    --dispatch-notes) DISPATCH_NOTES="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${ASSIGNMENT_ID}" || -z "${AGENT_REF}" || -z "${CHECKBOX_REF}" || -z "${BRANCH}" ]]; then
  echo "missing required arguments" >&2
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

python3 - "$COLLAB_PATH" "$ASSIGNMENT_ID" "$AGENT_REF" "$CHECKBOX_REF" "$CLAIM_KIND_REF" "$BRANCH" "$FROM_AGENT_REF" "$MESSAGE_ID" "$EVENT_ID" "$INITIAL_STATUS" "$COMMIT_SHA" "$ASSIGNMENT_NOTES" "$DISPATCH_NOTES" "$DRY_RUN" "${PAYLOAD_REFS[@]}" <<'PY'
import re
import sys
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
assignment_id = sys.argv[2]
agent_ref = sys.argv[3]
checkbox_ref = sys.argv[4]
claim_kind_ref = sys.argv[5]
branch = sys.argv[6]
from_agent_ref = sys.argv[7]
message_id_arg = sys.argv[8]
event_id_arg = sys.argv[9]
initial_status = sys.argv[10]
commit_sha = sys.argv[11]
assignment_notes = sys.argv[12]
dispatch_notes = sys.argv[13]
dry_run = sys.argv[14] == "1"
payload_refs = sys.argv[15:]

data = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
agents = {a.get("id"): a for a in data.get("agents", [])}
assignments = data.get("assignments", [])
messages = data.get("messages", [])
events = data.get("message_events", [])
claim_kinds = {c.get("id") for c in data.get("claim_kinds", [])}
dispatch_kind = data.get("worktree_governance", {}).get("assignment_dispatch_kind_ref", "MSGK_ASSIGNMENT_DISPATCH")
message_kinds = {k.get("id") for k in data.get("message_kinds", [])}
initial_statuses = set(data.get("message_transition_policy", {}).get("initial_statuses", []))

if not re.fullmatch(r"ASSIGN_[A-Z0-9_]+", assignment_id):
    raise SystemExit(f"invalid assignment id: {assignment_id}")
if assignment_id in {a.get("id") for a in assignments}:
    raise SystemExit(f"assignment already exists: {assignment_id}")
if agent_ref not in agents:
    raise SystemExit(f"unknown agent_ref: {agent_ref}")
if from_agent_ref not in agents:
    raise SystemExit(f"unknown from_agent_ref: {from_agent_ref}")
if claim_kind_ref not in claim_kinds:
    raise SystemExit(f"unknown claim_kind_ref: {claim_kind_ref}")
if not isinstance(checkbox_ref, str) or not re.fullmatch(r"[A-Z]{1,2}[0-9]+\.[0-9]+", checkbox_ref):
    raise SystemExit(f"invalid checkbox_ref: {checkbox_ref}")
if not isinstance(commit_sha, str) or not re.fullmatch(r"[0-9a-f]{7,40}", commit_sha):
    raise SystemExit(f"invalid commit sha: {commit_sha}")
if dispatch_kind not in message_kinds:
    raise SystemExit(f"dispatch kind not declared in message_kinds: {dispatch_kind}")
if initial_status not in initial_statuses:
    raise SystemExit(f"initial status {initial_status} not allowed by transition policy")

if message_id_arg:
    message_id = message_id_arg
else:
    message_id = f"MSG_{assignment_id.removeprefix('ASSIGN_')}_DISPATCH"
if not re.fullmatch(r"MSG_[A-Z0-9_]+", message_id):
    raise SystemExit(f"invalid message id: {message_id}")
if message_id in {m.get("id") for m in messages}:
    raise SystemExit(f"message id already exists: {message_id}")

if event_id_arg:
    event_id = event_id_arg
else:
    event_id = f"MSGEV_{assignment_id.removeprefix('ASSIGN_')}_DISPATCH_{initial_status.upper()}_1"
if not re.fullmatch(r"MSGEV_[A-Z0-9_]+", event_id):
    raise SystemExit(f"invalid event id: {event_id}")
if event_id in {e.get("id") for e in events}:
    raise SystemExit(f"event id already exists: {event_id}")

to_worktree = agents[agent_ref].get("worktree")
from_worktree = agents[from_agent_ref].get("worktree")
assignment = {
    "id": assignment_id,
    "agent_ref": agent_ref,
    "checkbox_ref": checkbox_ref,
    "claim_kind_ref": claim_kind_ref,
    "worktree": to_worktree,
    "branch": branch,
    "status": "assigned",
    "outcome": "pending",
    "notes": assignment_notes or f"Created via collab_create_assignment.sh for {checkbox_ref}.",
}
message = {
    "id": message_id,
    "kind_ref": dispatch_kind,
    "assignment_ref": assignment_id,
    "from_agent_ref": from_agent_ref,
    "to_agent_ref": agent_ref,
    "from_worktree": from_worktree,
    "to_worktree": to_worktree,
    "branch": branch,
    "initial_status": initial_status,
    "payload_refs": payload_refs,
    "evidence_refs": [],
    "evidence_bindings": [],
    "notes": dispatch_notes or f"Dispatch for {assignment_id} via collab_create_assignment.sh",
}
event = {
    "id": event_id,
    "message_ref": message_id,
    "from_status": None,
    "to_status": initial_status,
    "actor_agent_ref": from_agent_ref,
    "at_seq": 1,
    "commit": commit_sha,
    "evidence_bindings": [],
    "notes": f"Initial dispatch event for {assignment_id}.",
}

if dry_run:
    print("dry-run: validated create-assignment payload")
    print(f"assignment_id={assignment_id}")
    print(f"message_id={message_id}")
    print(f"event_id={event_id}")
    raise SystemExit(0)

assignments.append(assignment)
messages.append(message)
events.append(event)
data["assignments"] = assignments
data["messages"] = messages
data["message_events"] = events
collab_path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
print(f"created assignment+dispatch packet: {assignment_id} / {message_id}")
PY

if [[ "${DRY_RUN}" -eq 0 && "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

if [[ "${DRY_RUN}" -eq 0 ]]; then
  ./control-plane/scripts/collab_validate.sh >/dev/null
fi
