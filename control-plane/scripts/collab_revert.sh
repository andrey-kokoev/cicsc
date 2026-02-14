#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

MESSAGE_REF=""
TO_STATUS="sent"
REASON=""
ACTOR_AGENT_REF="AGENT_MAIN"
COMMIT_SHA=""
NO_REFRESH=0
DRY_RUN=0
FORCE=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_revert.sh --message-ref MSG_... --reason <text> [options]

Options:
  --to-status <s>        Target status after revert (sent|queued|rescinded; default: sent).
  --actor-agent-ref <id> Event actor (default: AGENT_MAIN).
  --commit <sha>         Commit to bind on event (default: current HEAD short).
  --no-refresh           Do not regenerate views after update.
  --dry-run              Validate and print action without mutation.
  --force                Override source-status guards (still subject to transition policy).
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --to-status) TO_STATUS="${2:-}"; shift 2 ;;
    --reason) REASON="${2:-}"; shift 2 ;;
    --actor-agent-ref) ACTOR_AGENT_REF="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --force) FORCE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${MESSAGE_REF}" || -z "${REASON}" ]]; then
  echo "--message-ref and --reason are required" >&2
  usage >&2
  exit 1
fi
if [[ "${#REASON}" -gt 240 ]]; then
  echo "--reason is too long (max 240 chars)" >&2
  exit 1
fi
case "${TO_STATUS}" in
  sent|queued|rescinded) ;;
  *) echo "unsupported --to-status '${TO_STATUS}'" >&2; exit 1 ;;
esac

cd "${ROOT_DIR}"
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
messages = {m.get("id"): m for m in collab.get("messages", [])}
if message_ref not in messages:
    raise SystemExit(f"unknown message_ref: {message_ref}")
events = [e for e in collab.get("message_events", []) if e.get("message_ref") == message_ref]
if not events:
    raise SystemExit(f"no events found for message {message_ref}")
events = sorted(events, key=lambda e: int(e.get("at_seq", 0)))
print(events[-1].get("to_status"))
PY
)"

if [[ "${FORCE}" -eq 0 ]]; then
  case "${CURRENT_STATUS}:${TO_STATUS}" in
    acknowledged:sent|acknowledged:queued|sent:queued|queued:sent|sent:rescinded|queued:rescinded) ;;
    *)
      echo "revert blocked: unsupported source->target without --force (${CURRENT_STATUS} -> ${TO_STATUS})" >&2
      echo "allowed without --force: acknowledged->sent|queued, sent->queued|rescinded, queued->sent|rescinded" >&2
      exit 1
      ;;
  esac
fi

notes="Reverted via collab_revert.sh: ${REASON}"

cmd=(
  ./control-plane/scripts/collab_append_event.sh
  --message-ref "${MESSAGE_REF}"
  --to-status "${TO_STATUS}"
  --actor-agent-ref "${ACTOR_AGENT_REF}"
  --commit "${COMMIT_SHA}"
  --notes "${notes}"
)
if [[ "${TO_STATUS}" == "rescinded" ]]; then
  cmd+=(--rescinded-reason "${REASON}")
fi
if [[ "${NO_REFRESH}" -eq 1 ]]; then
  cmd+=(--no-refresh)
fi
if [[ "${DRY_RUN}" -eq 1 ]]; then
  cmd+=(--dry-run)
fi

"${cmd[@]}"

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would revert ${MESSAGE_REF} to ${TO_STATUS}"
else
  ./control-plane/scripts/collab_validate.sh >/dev/null
  echo "reverted message: ${MESSAGE_REF} -> ${TO_STATUS}"
fi
