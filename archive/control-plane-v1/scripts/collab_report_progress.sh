#!/usr/bin/env bash
set -euo pipefail

# collab_report_progress.sh - Worker reports progress on acknowledged assignment
# Usage: ./control-plane/scripts/collab_report_progress.sh --message-ref MSG_PROGRESS_... --status "in_progress" [--notes "update"]

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

MESSAGE_REF=""
STATUS=""
NOTES=""
ELAPSED_MINUTES=""
ETA_MINUTES=""
DRY_RUN=0

cd "${ROOT_DIR}"

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_report_progress.sh --message-ref MSG_PROGRESS_... --status <status> [options]

Options:
  --message-ref <id>     The progress request message to respond to
  --status <status>      Current status: in_progress | blocked | nearing_completion
  --notes <text>         Detailed progress description
  --elapsed-minutes <n>  Time spent so far
  --eta-minutes <n>      Estimated time remaining
  --dry-run              Validate only, do not append event
  -h, --help             Show this message

Status meanings:
  in_progress        - Actively working, no blockers
  blocked            - Stuck, need assistance (also consider friction request)
  nearing_completion - Expected to fulfill within ETA

Example:
  ./control-plane/scripts/collab_report_progress.sh \
    --message-ref MSG_PROGRESS_AY13_GEMINI_20260214T230000Z \
    --status in_progress \
    --notes "Implemented core logic, running conformance tests" \
    --elapsed-minutes 90 \
    --eta-minutes 30
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --status) STATUS="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --elapsed-minutes) ELAPSED_MINUTES="${2:-}"; shift 2 ;;
    --eta-minutes) ETA_MINUTES="${2:-}"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${MESSAGE_REF}" ]]; then
  echo "error: --message-ref is required" >&2
  exit 1
fi

if [[ -z "${STATUS}" ]]; then
  echo "error: --status is required" >&2
  exit 1
fi

if [[ "${STATUS}" != "in_progress" && "${STATUS}" != "blocked" && "${STATUS}" != "nearing_completion" ]]; then
  echo "error: --status must be in_progress, blocked, or nearing_completion" >&2
  exit 1
fi

echo "Reporting progress for: ${MESSAGE_REF}"
echo "  Status: ${STATUS}"
[[ -n "${NOTES}" ]] && echo "  Notes: ${NOTES}"
[[ -n "${ELAPSED_MINUTES}" ]] && echo "  Elapsed: ${ELAPSED_MINUTES}m"
[[ -n "${ETA_MINUTES}" ]] && echo "  ETA: ${ETA_MINUTES}m"

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "DRY RUN: would append progress report event"
  exit 0
fi

# Append progress report event
python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$MESSAGE_REF" "$STATUS" "$NOTES" "$ELAPSED_MINUTES" "$ETA_MINUTES" <<'PY'
import sys
import yaml
from pathlib import Path
from datetime import datetime, timezone

model_path = Path(sys.argv[1])
doc = yaml.safe_load(model_path.read_text(encoding="utf-8"))

msg_ref = sys.argv[2]
status = sys.argv[3]
notes = sys.argv[4]
elapsed = sys.argv[5]
eta = sys.argv[6]

# Get current sequence
seq = max([int(e.get("at_seq", 0)) for e in doc.get("message_events", [])] + [0]) + 1

# Build progress details
progress_notes = f"Status: {status}"
if notes:
    progress_notes += f" | {notes}"
if elapsed:
    progress_notes += f" | Elapsed: {elapsed}m"
if eta:
    progress_notes += f" | ETA: {eta}m"

# Add progress report event (this is an information event, not status change)
event = {
    "id": f"MSGEV_{msg_ref}_PROGRESS_{seq}",
    "message_ref": msg_ref,
    "from_status": "sent",
    "to_status": "sent",  # Status doesn't change, we just add info
    "at_seq": seq,
    "timestamp": datetime.now(timezone.utc).isoformat(),
    "actor_agent_ref": "AGENT_GEMINI",  # Should be detected from context
    "evidence": [],
    "notes": progress_notes,
}

doc["message_events"].append(event)
model_path.write_text(yaml.dump(doc, sort_keys=False, allow_unicode=True), encoding="utf-8")
print(f"Progress reported: {progress_notes}")
PY

./control-plane/scripts/generate_views.sh >/dev/null

echo "Progress report sent to Main"
