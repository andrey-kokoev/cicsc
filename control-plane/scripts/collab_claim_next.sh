#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
WORKTREE="${PWD}"
MESSAGE_REF=""
COMMIT_SHA=""
NOTES=""
NO_REFRESH=0
DRY_RUN=0
FORCE=0
AUTO_COMMIT=0
COMMIT_SUBJECT=""
COMMIT_BODY=()

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
  --force               Allow claiming new sent/queued messages even when acknowledged work exists.
  --auto-commit         Auto-commit collab model/views after successful claim (requires clean tree).
  --commit-subject <t>  Commit subject override when --auto-commit is set.
  --commit-body <t>     Additional commit body line (repeatable) for --auto-commit.
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
    --force) FORCE=1; shift ;;
    --auto-commit) AUTO_COMMIT=1; shift ;;
    --commit-subject) COMMIT_SUBJECT="${2:-}"; shift 2 ;;
    --commit-body) COMMIT_BODY+=("${2:-}"); shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

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

if [[ "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

_resolved="$(
python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$ROOT_DIR/control-plane/views/worktree-mailboxes.generated.json" "$WORKTREE" "$MESSAGE_REF" "$FORCE" <<'PY'
import json
import sys
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
mailbox_path = Path(sys.argv[2])
worktree = sys.argv[3]
message_ref = sys.argv[4]
force = sys.argv[5] == "1"

collab = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
mailboxes = json.loads(mailbox_path.read_text(encoding="utf-8")).get("mailboxes", {})
entry = mailboxes.get(worktree, {"inbox": []})
inbox = entry.get("inbox", [])
acknowledged = sorted(
    [m for m in inbox if m.get("current_status") == "acknowledged"],
    key=lambda m: m.get("id", "")
)
if acknowledged and not force:
    print("BLOCKED_ACKNOWLEDGED")
    for m in acknowledged:
        print(m.get("id"))
    raise SystemExit(0)

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

if force and acknowledged:
    print("FORCE_OVERRIDE_ACKNOWLEDGED")
    print(",".join(m.get("id", "") for m in acknowledged if m.get("id")))

print(msg.get("id"))
print(agent.get("id"))
print(msg.get("assignment_ref"))
PY
)" || {
  echo "failed to resolve claim target for worktree ${WORKTREE}" >&2
  exit 1
}

if [[ "${_resolved}" == "NO_ACTIONABLE" ]]; then
  echo "no actionable inbox messages for ${WORKTREE}"
  exit 0
fi

if [[ "${_resolved}" == BLOCKED_ACKNOWLEDGED* ]]; then
  readarray -t _blk <<<"${_resolved}"
  echo "claim blocked: worktree ${WORKTREE} has acknowledged messages that must be fulfilled first" >&2
  for ((i=1; i<${#_blk[@]}; i++)); do
    [[ -n "${_blk[$i]}" ]] && echo " - ${_blk[$i]}" >&2
  done
  echo "use --force to override" >&2
  exit 1
fi

readarray -t _lines <<<"${_resolved}"
line_ix=0
FORCED_ACK_IDS=""
if [[ "${_lines[0]}" == "FORCE_OVERRIDE_ACKNOWLEDGED" ]]; then
  FORCED_ACK_IDS="${_lines[1]}"
  line_ix=2
  echo "warning: --force override used; claiming new actionable message while acknowledged work exists: ${FORCED_ACK_IDS}" >&2
fi
MESSAGE_REF="${_lines[$line_ix]}"
ACTOR_AGENT="${_lines[$((line_ix + 1))]}"
ASSIGNMENT_REF="${_lines[$((line_ix + 2))]}"

if [[ -z "${NOTES}" ]]; then
  NOTES="Acknowledged by ${ACTOR_AGENT} via collab_claim_next.sh"
fi
if [[ -n "${FORCED_ACK_IDS}" ]]; then
  NOTES="${NOTES}; force_override_acknowledged=${FORCED_ACK_IDS}"
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
  echo "run: ./control-plane/scripts/collab_show_assignment.sh --ref ${ASSIGNMENT_REF}"
else
  echo "claimed message: ${MESSAGE_REF}"
  echo "run: ./control-plane/scripts/collab_show_assignment.sh --ref ${ASSIGNMENT_REF}"
  if [[ "${AUTO_COMMIT}" -eq 1 ]]; then
    _commit_cmd=(./control-plane/scripts/collab_commit_views.sh --from-last-collab-action)
    if [[ -n "${COMMIT_SUBJECT}" ]]; then
      _commit_cmd+=(--subject "${COMMIT_SUBJECT}")
    fi
    for line in "${COMMIT_BODY[@]}"; do
      _commit_cmd+=(--body "${line}")
    done
    "${_commit_cmd[@]}"
    echo "auto-committed collab model/views"
  fi
fi
