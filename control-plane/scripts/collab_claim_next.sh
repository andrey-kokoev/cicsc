#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORKTREE="${PWD}"
MESSAGE_REF=""
COMMIT_SHA=""
NOTES=""
NO_REFRESH=0
DRY_RUN=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_claim_next.sh [options]

Options:
  --worktree <path>     Worktree path key (default: current $PWD).
  --message-ref <id>    Explicit message to acknowledge. If omitted, first actionable message is selected.
  --commit <sha>        Commit to bind on event (default: current HEAD short).
  --notes <text>        Optional event note.
  --no-refresh          Do not regenerate mailbox projection before reading.
  --dry-run             Resolve target and validate, but do not append event.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

if [[ "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

_resolved="$(
python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$ROOT_DIR/control-plane/views/worktree-mailboxes.generated.json" "$WORKTREE" "$MESSAGE_REF" <<'PY'
import json
import sys
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
mailbox_path = Path(sys.argv[2])
worktree = sys.argv[3]
message_ref = sys.argv[4]

collab = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
mailboxes = json.loads(mailbox_path.read_text(encoding="utf-8")).get("mailboxes", {})
entry = mailboxes.get(worktree, {"inbox": []})
inbox = entry.get("inbox", [])
actionable = [m for m in inbox if m.get("current_status") in {"queued", "sent"}]
if not actionable:
    if message_ref:
        raise SystemExit(f"message {message_ref} is not actionable in inbox for {worktree}")
    print("NO_ACTIONABLE")
    raise SystemExit(0)

if message_ref:
    msg = next((m for m in actionable if m.get("id") == message_ref), None)
    if msg is None:
        raise SystemExit(f"message {message_ref} is not actionable in inbox for {worktree}")
else:
    # Prefer sent over queued, then stable id order.
    sent = sorted([m for m in actionable if m.get("current_status") == "sent"], key=lambda m: m.get("id", ""))
    queued = sorted([m for m in actionable if m.get("current_status") == "queued"], key=lambda m: m.get("id", ""))
    msg = sent[0] if sent else queued[0]

agents = collab.get("agents", [])
agent = next((a for a in agents if a.get("worktree") == worktree), None)
if agent is None:
    raise SystemExit(f"no agent mapped to worktree {worktree}")

print(msg.get("id"))
print(agent.get("id"))
PY
)" || {
  echo "failed to resolve claim target for worktree ${WORKTREE}" >&2
  exit 1
}

if [[ "${_resolved}" == "NO_ACTIONABLE" ]]; then
  echo "no actionable inbox messages for ${WORKTREE}"
  exit 0
fi

readarray -t _lines <<<"${_resolved}"
MESSAGE_REF="${_lines[0]}"
ACTOR_AGENT="${_lines[1]}"

if [[ -z "${NOTES}" ]]; then
  NOTES="Acknowledged by ${ACTOR_AGENT} via collab_claim_next.sh"
fi

./control-plane/scripts/collab_append_event.sh \
  --message-ref "${MESSAGE_REF}" \
  --to-status acknowledged \
  --actor-agent-ref "${ACTOR_AGENT}" \
  --commit "${COMMIT_SHA}" \
  --notes "${NOTES}" \
  $([[ "${DRY_RUN}" -eq 1 ]] && echo --dry-run)

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would claim message ${MESSAGE_REF}"
else
  echo "claimed message: ${MESSAGE_REF}"
fi
