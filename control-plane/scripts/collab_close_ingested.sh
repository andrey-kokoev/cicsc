#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MESSAGE_REF=""
ACTOR_AGENT_REF="AGENT_MAIN"
COMMIT_SHA=""
NO_REFRESH=0
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

if [[ "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

echo "message close path complete: ${MESSAGE_REF} (from ${CURRENT_STATUS})"
