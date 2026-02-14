#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE=""
AGENT_REF=""
MESSAGE_REFS=()
ASSIGNMENT_REFS=()
RUN_REF=""
TARGET_STATUS="fulfilled"
COUNT=0
ACTOR_AGENT_REF="AGENT_MAIN"
COMMIT_SHA=""
NO_COMMIT=0
DRY_RUN=0
SUBJECT=""
BODY=()
SILENT_EMPTY=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_close_batch.sh [options]

Options:
  --worktree <path>       Filter candidates by message to_worktree.
  --agent-ref <id>        Filter candidates by message to_agent_ref.
  --message-ref <id>      Explicit message ref to close (repeatable).
  --assignment-ref <id>   Explicit assignment ref to close (repeatable).
  --run <id|path>         Select messages from a dispatch run journal.
  --status <s>            Candidate status: fulfilled|ingested (default: fulfilled).
  --count <n>             Max candidate messages when auto-selecting (0 = all).
  --actor-agent-ref <id>  Actor for emitted close events (default: AGENT_MAIN).
  --commit <sha>          Commit to bind on emitted events (default: current HEAD short).
  --subject <text>        Commit subject override.
  --body <text>           Commit body line (repeatable).
  --silent-empty          Exit silently when no messages are selected.
  --no-commit             Do not commit after close batch.
  --dry-run               Resolve plan and validate only.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --agent-ref) AGENT_REF="${2:-}"; shift 2 ;;
    --message-ref) MESSAGE_REFS+=("${2:-}"); shift 2 ;;
    --assignment-ref) ASSIGNMENT_REFS+=("${2:-}"); shift 2 ;;
    --run) RUN_REF="${2:-}"; shift 2 ;;
    --status) TARGET_STATUS="${2:-}"; shift 2 ;;
    --count) COUNT="${2:-}"; shift 2 ;;
    --actor-agent-ref) ACTOR_AGENT_REF="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --subject) SUBJECT="${2:-}"; shift 2 ;;
    --body) BODY+=("${2:-}"); shift 2 ;;
    --silent-empty) SILENT_EMPTY=1; shift ;;
    --no-commit) NO_COMMIT=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ "${TARGET_STATUS}" != "fulfilled" && "${TARGET_STATUS}" != "ingested" ]]; then
  echo "--status must be fulfilled or ingested" >&2
  exit 1
fi
if ! [[ "${COUNT}" =~ ^[0-9]+$ ]]; then
  echo "--count must be >= 0" >&2
  exit 1
fi

cd "${ROOT_DIR}"
if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi
if [[ "${NO_COMMIT}" -eq 0 && "${DRY_RUN}" -eq 0 && -n "$(git status --porcelain)" ]]; then
  echo "batch close with commit requires a clean working tree" >&2
  exit 1
fi

./control-plane/scripts/collab_validate.sh >/dev/null

if [[ ${#MESSAGE_REFS[@]} -eq 0 ]]; then
  mapfile -t MESSAGE_REFS < <(python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$WORKTREE" "$AGENT_REF" "$TARGET_STATUS" "$COUNT" "$RUN_REF" "${ASSIGNMENT_REFS[@]}" <<'PY'
import sys
import json
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
worktree = sys.argv[2]
agent_ref = sys.argv[3]
target_status = sys.argv[4]
count = int(sys.argv[5])
run_ref = sys.argv[6]
assignment_refs = {x for x in sys.argv[7:] if x}

messages = {m.get("id"): m for m in collab.get("messages", [])}
events_by = {}
for ev in collab.get("message_events", []):
    events_by.setdefault(ev.get("message_ref"), []).append(ev)

run_message_refs = set()
if run_ref:
    rp = Path(run_ref)
    if not rp.exists():
        rp2 = Path("control-plane/logs/dispatch-runs") / f"{run_ref}.json"
        if rp2.exists():
            rp = rp2
    if not rp.exists():
        raise SystemExit(f"run file not found: {run_ref}")
    run_doc = json.loads(rp.read_text(encoding="utf-8"))
    run_message_refs = {r.get("message_id") for r in run_doc.get("rows", []) if r.get("message_id")}

rows = []
for mid, msg in messages.items():
    if run_message_refs and mid not in run_message_refs:
        continue
    if assignment_refs and msg.get("assignment_ref") not in assignment_refs:
        continue
    if worktree and msg.get("to_worktree") != worktree:
        continue
    if agent_ref and msg.get("to_agent_ref") != agent_ref:
        continue
    evs = sorted(events_by.get(mid, []), key=lambda e: int(e.get("at_seq", 0)))
    if not evs:
        continue
    cur = evs[-1].get("to_status")
    if cur != target_status:
        continue
    rows.append((int(evs[-1].get("at_seq", 0)), mid))

rows.sort()
if count > 0:
    rows = rows[:count]
for _, mid in rows:
    print(mid)
PY
)
fi

if [[ ${#MESSAGE_REFS[@]} -eq 0 ]]; then
  if [[ "${SILENT_EMPTY}" -eq 0 ]]; then
    echo "no messages selected for batch close"
  fi
  exit 0
fi

echo "batch-close messages (${#MESSAGE_REFS[@]}):"
printf ' - %s\n' "${MESSAGE_REFS[@]}"

for mref in "${MESSAGE_REFS[@]}"; do
  cmd=(
    ./control-plane/scripts/collab_close_ingested.sh
    --message-ref "${mref}"
    --actor-agent-ref "${ACTOR_AGENT_REF}"
    --commit "${COMMIT_SHA}"
    --no-refresh
  )
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    cmd+=(--dry-run)
  fi
  "${cmd[@]}"
done

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: batch close validated"
  exit 0
fi

./control-plane/scripts/generate_views.sh >/dev/null
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ "${NO_COMMIT}" -eq 0 ]]; then
  if [[ -z "${SUBJECT}" ]]; then
    commit_cmd=(./control-plane/scripts/collab_commit_views.sh --from-last-collab-action --no-refresh)
  else
    commit_cmd=(./control-plane/scripts/collab_commit_views.sh --subject "${SUBJECT}" --no-refresh)
  fi
  if [[ ${#BODY[@]} -eq 0 ]]; then
    commit_cmd+=(--body "Batch close actor: ${ACTOR_AGENT_REF}" --body "Batch close source status: ${TARGET_STATUS}")
  else
    for line in "${BODY[@]}"; do
      commit_cmd+=(--body "${line}")
    done
  fi
  "${commit_cmd[@]}"
fi

echo "batch close complete"
