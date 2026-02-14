#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
MESSAGE_REF=""
WORKTREE="${PWD}"
ACTOR_AGENT=""
COMMIT_SHA=""
NOTES=""
NO_REFRESH=0
DRY_RUN=0
SUGGEST_COMMIT=0
SCRIPT_REFS=()
GATE_REFS=()
THEOREM_REFS=()
DIFFLOG_REFS=()
RAW_EVIDENCE=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_fulfill.sh --message-ref MSG_... [options]

Options:
  --worktree <path>     Worktree path key (default: current $PWD).
  --actor-agent-ref <id>
                        Explicit actor override (default: owner agent of worktree).
  --commit <sha>        Commit to bind on event (default: current HEAD short).
  --notes <text>        Optional event note.
  --script <path>       Add evidence binding with kind EVID_SCRIPT.
  --gate-report <path>  Add evidence binding with kind EVID_GATE_REPORT.
  --theorem <path>      Add evidence binding with kind EVID_THEOREM.
  --diff-log <path>     Add evidence binding with kind EVID_DIFFERENTIAL_LOG.
  --evidence <ref|EVID_KIND>
                        Add custom typed evidence (digest auto-computed from ref path).
  --no-refresh          Do not regenerate mailbox projection after append.
  --dry-run             Validate and resolve evidence bindings, but do not append event.
  --suggest-commit      Print a suggested git commit command after fulfill.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --actor-agent-ref) ACTOR_AGENT="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --script) SCRIPT_REFS+=("${2:-}"); shift 2 ;;
    --gate-report) GATE_REFS+=("${2:-}"); shift 2 ;;
    --theorem) THEOREM_REFS+=("${2:-}"); shift 2 ;;
    --diff-log) DIFFLOG_REFS+=("${2:-}"); shift 2 ;;
    --evidence) RAW_EVIDENCE+=("${2:-}"); shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --suggest-commit) SUGGEST_COMMIT=1; shift ;;
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
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

if [[ -z "${ACTOR_AGENT}" ]]; then
  ACTOR_AGENT="$(
    python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$WORKTREE" <<'PY'
import sys
from pathlib import Path
import yaml
collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
worktree = sys.argv[2]
agent = next((a for a in collab.get("agents", []) if a.get("worktree") == worktree), None)
if agent is None:
    raise SystemExit(f"no agent mapped to worktree {worktree}")
print(agent.get("id"))
PY
  )"
fi

if [[ -z "${NOTES}" ]]; then
  NOTES="Fulfilled by ${ACTOR_AGENT} via collab_fulfill.sh"
fi

to_rel_path() {
  python3 - "$ROOT_DIR" "$1" <<'PY'
import os, sys
root = os.path.abspath(sys.argv[1])
path = sys.argv[2]
ap = os.path.abspath(path if os.path.isabs(path) else os.path.join(root, path))
if not ap.startswith(root + os.sep):
    raise SystemExit(f"path outside repo: {path}")
print(os.path.relpath(ap, root))
PY
}

mk_evidence_item() {
  local ref="$1"
  local kind="$2"
  local rel
  rel="$(to_rel_path "${ref}")"
  if [[ ! -f "${ROOT_DIR}/${rel}" ]]; then
    echo "missing evidence file: ${rel}" >&2
    exit 1
  fi
  local digest
  digest="$(sha256sum "${ROOT_DIR}/${rel}" | awk '{print $1}')"
  echo "${rel}|${kind}|${COMMIT_SHA}|sha256:${digest}"
}

EVIDENCE_ITEMS=()
for ref in "${SCRIPT_REFS[@]}"; do
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "EVID_SCRIPT")")
done
for ref in "${GATE_REFS[@]}"; do
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "EVID_GATE_REPORT")")
done
for ref in "${THEOREM_REFS[@]}"; do
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "EVID_THEOREM")")
done
for ref in "${DIFFLOG_REFS[@]}"; do
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "EVID_DIFFERENTIAL_LOG")")
done
for item in "${RAW_EVIDENCE[@]}"; do
  kind="${item##*|}"
  ref="${item%|*}"
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "${kind}")")
done

if [[ ${#EVIDENCE_ITEMS[@]} -eq 0 ]]; then
  echo "at least one evidence binding is required for fulfill" >&2
  exit 1
fi

cmd=(
  ./control-plane/scripts/collab_append_event.sh
  --message-ref "${MESSAGE_REF}"
  --to-status fulfilled
  --actor-agent-ref "${ACTOR_AGENT}"
  --commit "${COMMIT_SHA}"
  --notes "${NOTES}"
)
if [[ "${NO_REFRESH}" -eq 1 ]]; then
  cmd+=(--no-refresh)
fi
if [[ "${DRY_RUN}" -eq 1 ]]; then
  cmd+=(--dry-run)
fi
for e in "${EVIDENCE_ITEMS[@]}"; do
  cmd+=(--evidence "${e}")
done

"${cmd[@]}"
if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would fulfill message ${MESSAGE_REF}"
else
  ./control-plane/scripts/collab_validate.sh >/dev/null
  _summary="$(
    python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$MESSAGE_REF" "$WORKTREE" <<'PY'
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
message_ref = sys.argv[2]
worktree = sys.argv[3]
messages = collab.get("messages", [])
events = collab.get("message_events", [])

msg = next((m for m in messages if m.get("id") == message_ref), None)
if msg is None:
    raise SystemExit("unknown message")
assignment_ref = msg.get("assignment_ref")
assignments = {a.get("id"): a for a in collab.get("assignments", [])}
checkbox_ref = (assignments.get(assignment_ref) or {}).get("checkbox_ref", "")

events_by_message = {}
for e in events:
    events_by_message.setdefault(e.get("message_ref"), []).append(e)

remaining = 0
for m in messages:
    if m.get("to_worktree") != worktree:
        continue
    evs = sorted(events_by_message.get(m.get("id"), []), key=lambda e: int(e.get("at_seq", 0)))
    cur = evs[-1].get("to_status") if evs else m.get("initial_status")
    if cur in {"queued", "sent"}:
        remaining += 1

print(assignment_ref)
print(checkbox_ref)
print(remaining)
PY
  )"
  readarray -t _sum_lines <<<"${_summary}"
  _assignment_ref="${_sum_lines[0]}"
  _checkbox_ref="${_sum_lines[1]}"
  _remaining="${_sum_lines[2]}"
  echo "fulfilled message: ${MESSAGE_REF}"
  echo "assignment: ${_assignment_ref}"
  echo "remaining actionable in ${WORKTREE}: ${_remaining}"
  if [[ "${SUGGEST_COMMIT}" -eq 1 ]]; then
    _subject="governance/collab: fulfill ${_assignment_ref}"
    if [[ -n "${_checkbox_ref}" ]]; then
      _subject="governance/collab: fulfill ${_checkbox_ref} (${_assignment_ref})"
    fi
    echo "suggested commit:"
    echo "git add control-plane/collaboration/collab-model.yaml control-plane/views/ && \\"
    echo "  git commit -m \"${_subject}\""
  fi
fi
