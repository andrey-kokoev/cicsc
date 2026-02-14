#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
MESSAGE_REF=""
ACTOR_AGENT_REF="AGENT_MAIN"
COMMIT_SHA=""
NO_REFRESH=0
DRY_RUN=0
AUTO_COMMIT=0
INGESTED_NOTES=""
CLOSED_NOTES=""

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_close_ingested.sh --message-ref MSG_... [options]

Options:
  --actor-agent-ref <id>  Actor for emitted events (default: AGENT_MAIN).
  --commit <sha>          Commit to bind on emitted events (default: current HEAD short).
  --ingested-notes <txt>  Optional notes for ingested event.
  --closed-notes <txt>    Optional notes for closed event.
  --no-refresh            Do not regenerate views after update.
  --dry-run               Validate and print closure actions without mutation.
  --auto-commit           Auto-commit collab model/views after close (requires clean tree).
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --actor-agent-ref) ACTOR_AGENT_REF="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --ingested-notes) INGESTED_NOTES="${2:-}"; shift 2 ;;
    --closed-notes) CLOSED_NOTES="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --auto-commit) AUTO_COMMIT=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${MESSAGE_REF}" ]]; then
  echo "--message-ref is required" >&2
  usage >&2
  exit 1
fi

cd "${ROOT_DIR}"
if [[ "${AUTO_COMMIT}" -eq 1 && "${DRY_RUN}" -eq 0 ]]; then
  if [[ -n "$(git status --porcelain)" ]]; then
    echo "auto-commit requires a clean working tree" >&2
    exit 1
  fi
fi
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

CURRENT_STATUS="$(
  python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$MESSAGE_REF" <<'PY'
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
message_ref = sys.argv[2]
events = [e for e in collab.get("message_events", []) if e.get("message_ref") == message_ref]
if not events:
    raise SystemExit(f"no events found for message {message_ref}")
events = sorted(events, key=lambda e: int(e.get("at_seq", 0)))
print(events[-1].get("to_status"))
PY
)"

case "${CURRENT_STATUS}" in
  fulfilled)
    if [[ -z "${INGESTED_NOTES}" ]]; then
      INGESTED_NOTES="Ingested in main via collab_close_ingested.sh"
    fi
    ./control-plane/scripts/collab_append_event.sh \
      --message-ref "${MESSAGE_REF}" \
      --to-status ingested \
      --actor-agent-ref "${ACTOR_AGENT_REF}" \
      --commit "${COMMIT_SHA}" \
      --notes "${INGESTED_NOTES}" \
      $([[ "${DRY_RUN}" -eq 1 ]] && echo --dry-run) \
      --no-refresh
    ;&
  ingested)
    if [[ -z "${CLOSED_NOTES}" ]]; then
      CLOSED_NOTES="Closed in main via collab_close_ingested.sh"
    fi
    ./control-plane/scripts/collab_append_event.sh \
      --message-ref "${MESSAGE_REF}" \
      --to-status closed \
      --actor-agent-ref "${ACTOR_AGENT_REF}" \
      --commit "${COMMIT_SHA}" \
      --notes "${CLOSED_NOTES}" \
      $([[ "${DRY_RUN}" -eq 1 ]] && echo --dry-run) \
      --no-refresh
    ;;
  closed)
    echo "message already closed: ${MESSAGE_REF}"
    ;;
  *)
    echo "cannot close message from status '${CURRENT_STATUS}' (expected fulfilled|ingested|closed)" >&2
    exit 1
    ;;
esac

if [[ "${DRY_RUN}" -eq 0 ]]; then
python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$MESSAGE_REF" <<'PY'
import sys
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
message_ref = sys.argv[2]
data = yaml.safe_load(collab_path.read_text(encoding="utf-8"))

messages = {m.get("id"): m for m in data.get("messages", [])}
msg = messages.get(message_ref)
if msg is None:
    raise SystemExit(f"message not found: {message_ref}")

assignment_ref = msg.get("assignment_ref")
assignments = data.get("assignments", [])
assignment = next((a for a in assignments if a.get("id") == assignment_ref), None)
if assignment is None:
    raise SystemExit(f"assignment not found for message: {assignment_ref}")

events = [e for e in data.get("message_events", []) if e.get("message_ref") == message_ref]
events = sorted(events, key=lambda e: int(e.get("at_seq", 0)))
if not events:
    raise SystemExit(f"no events for message: {message_ref}")

terminal = events[-1].get("to_status")
if terminal not in {"closed", "rescinded"}:
    # Only synchronize assignment on terminal message states.
    raise SystemExit(0)

assigned_agent = assignment.get("agent_ref")
has_assignee_fulfilled = any(
    e.get("to_status") == "fulfilled" and e.get("actor_agent_ref") == assigned_agent
    for e in events
)

if terminal == "closed":
    assignment["status"] = "done"
    assignment["outcome"] = "fulfilled_by_assignee" if has_assignee_fulfilled else "fulfilled_by_main"
elif terminal == "rescinded":
    assignment["status"] = "done"
    assignment["outcome"] = "fulfilled_by_main"

data["assignments"] = assignments
collab_path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
print(f"synchronized assignment {assignment_ref} -> {assignment['status']}/{assignment['outcome']}")
PY
else
  echo "dry-run: would synchronize assignment for ${MESSAGE_REF}"
fi

if [[ "${DRY_RUN}" -eq 0 && "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

if [[ "${DRY_RUN}" -eq 0 ]]; then
  ./control-plane/scripts/collab_validate.sh >/dev/null
  echo "message close path complete: ${MESSAGE_REF} (from ${CURRENT_STATUS})"
  if [[ "${AUTO_COMMIT}" -eq 1 ]]; then
    ./control-plane/scripts/collab_commit_views.sh --from-last-collab-action
    echo "auto-committed collab model/views"
  fi
else
  echo "dry-run: close path validated for ${MESSAGE_REF} (from ${CURRENT_STATUS})"
fi
