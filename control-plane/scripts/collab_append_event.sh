#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
COLLAB_PATH="${ROOT_DIR}/control-plane/collaboration/collab-model.yaml"

MESSAGE_REF=""
TO_STATUS=""
ACTOR=""
COMMIT_SHA=""
FROM_STATUS=""
EVENT_ID=""
NOTES=""
RESCINDED_REASON=""
NO_REFRESH=0
DRY_RUN=0
EVIDENCE_ITEMS=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_append_event.sh \
    --message-ref MSG_... \
    --to-status <status> \
    --actor-agent-ref AGENT_... \
    --commit <sha7..40> \
    [--from-status <status|null>] \
    [--event-id MSGEV_...] \
    [--notes "<text>"] \
    [--rescinded-reason "<text>"] \
    [--evidence "ref|EVID_KIND|commit|sha256:digest"] ... \
    [--no-refresh]

Notes:
  - at_seq is auto-assigned as max(existing)+1 for the message.
  - if --event-id is omitted, a deterministic id is generated.
  - --from-status defaults to previous event's to_status (or null at sequence start).
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --message-ref)
      MESSAGE_REF="${2:-}"
      shift 2
      ;;
    --to-status)
      TO_STATUS="${2:-}"
      shift 2
      ;;
    --actor-agent-ref)
      ACTOR="${2:-}"
      shift 2
      ;;
    --commit)
      COMMIT_SHA="${2:-}"
      shift 2
      ;;
    --from-status)
      FROM_STATUS="${2:-}"
      shift 2
      ;;
    --event-id)
      EVENT_ID="${2:-}"
      shift 2
      ;;
    --notes)
      NOTES="${2:-}"
      shift 2
      ;;
    --rescinded-reason)
      RESCINDED_REASON="${2:-}"
      shift 2
      ;;
    --evidence)
      EVIDENCE_ITEMS+=("${2:-}")
      shift 2
      ;;
    --no-refresh)
      NO_REFRESH=1
      shift
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

if [[ -z "${MESSAGE_REF}" || -z "${TO_STATUS}" || -z "${ACTOR}" || -z "${COMMIT_SHA}" ]]; then
  echo "missing required arguments" >&2
  usage >&2
  exit 1
fi

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

python3 - "$COLLAB_PATH" "$MESSAGE_REF" "$TO_STATUS" "$ACTOR" "$COMMIT_SHA" "$FROM_STATUS" "$EVENT_ID" "$NOTES" "$RESCINDED_REASON" "$DRY_RUN" "${EVIDENCE_ITEMS[@]}" <<'PY'
import re
import sys
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
message_ref = sys.argv[2]
to_status = sys.argv[3]
actor = sys.argv[4]
commit_sha = sys.argv[5]
from_status_arg = sys.argv[6]
event_id_arg = sys.argv[7]
notes_arg = sys.argv[8]
rescinded_reason_arg = sys.argv[9]
dry_run = sys.argv[10] == "1"
evidence_items = sys.argv[11:]

data = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
messages = data.get("messages", [])
events = data.get("message_events", [])
agents = {a.get("id") for a in data.get("agents", [])}

if message_ref not in {m.get("id") for m in messages}:
    raise SystemExit(f"unknown message_ref: {message_ref}")
if actor not in agents:
    raise SystemExit(f"unknown actor agent: {actor}")
if not re.fullmatch(r"[0-9a-f]{7,40}", commit_sha):
    raise SystemExit(f"invalid commit sha: {commit_sha}")

m_events = [e for e in events if e.get("message_ref") == message_ref]
max_seq = max((int(e.get("at_seq", 0)) for e in m_events), default=0)
next_seq = max_seq + 1

prev_status = None
if max_seq > 0:
    prev = sorted(m_events, key=lambda e: int(e.get("at_seq", 0)))[-1]
    prev_status = prev.get("to_status")

if from_status_arg == "":
    from_status = prev_status
elif from_status_arg == "null":
    from_status = None
else:
    from_status = from_status_arg

if event_id_arg:
    event_id = event_id_arg
else:
    base = message_ref.removeprefix("MSG_")
    suffix = re.sub(r"[^A-Z0-9_]", "_", to_status.upper())
    event_id = f"MSGEV_{base}_{suffix}_{next_seq}"

if event_id in {e.get("id") for e in events}:
    raise SystemExit(f"duplicate event id: {event_id}")

bindings = []
for item in evidence_items:
    parts = item.split("|")
    if len(parts) != 4:
        raise SystemExit(
            f"invalid evidence item '{item}' (expected ref|EVID_KIND|commit|sha256:digest)"
        )
    ref, kind, bcommit, digest = parts
    bindings.append(
        {
            "ref": ref,
            "evidence_kind_ref": kind,
            "commit": bcommit,
            "digest": digest,
        }
    )

event = {
    "id": event_id,
    "message_ref": message_ref,
    "from_status": from_status,
    "to_status": to_status,
    "actor_agent_ref": actor,
    "at_seq": next_seq,
    "commit": commit_sha,
    "evidence_bindings": bindings,
}
if rescinded_reason_arg:
    event["rescinded_reason"] = rescinded_reason_arg
if notes_arg:
    event["notes"] = notes_arg

if dry_run:
    print(f"dry-run: would append event {event_id} to {collab_path}")
    raise SystemExit(0)

events.append(event)
data["message_events"] = events
collab_path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
print(f"appended event {event_id} to {collab_path}")
PY

if [[ "${DRY_RUN}" -eq 0 && "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

if [[ "${DRY_RUN}" -eq 0 ]]; then
  ./control-plane/scripts/collab_validate.sh >/dev/null
  echo "appended event to ${COLLAB_PATH}"
fi
