#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
SUBJECT="governance/collab: commit model and generated views"
SUBJECT_EXPLICIT=0
BODY=()
DRY_RUN=0
NO_REFRESH=0
FROM_LAST_COLLAB_ACTION=0
EDIT_BODY=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_commit_views.sh [options]

Options:
  --subject <text>    Commit subject (default provided).
  --body <text>       Additional commit body line (repeatable).
  --no-refresh        Do not run generate_views before staging.
  --from-last-collab-action
                      Derive commit subject/body from latest message_event.
  --edit-body         Open commit editor for body/note editing.
  --dry-run           Show staged files and commit command, do not commit.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --subject) SUBJECT="${2:-}"; SUBJECT_EXPLICIT=1; shift 2 ;;
    --body) BODY+=("${2:-}"); shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --from-last-collab-action) FROM_LAST_COLLAB_ACTION=1; shift ;;
    --edit-body) EDIT_BODY=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"

if [[ "${FROM_LAST_COLLAB_ACTION}" -eq 1 ]]; then
  _derived="$(
    python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" <<'PY'
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
events = sorted(collab.get("message_events", []), key=lambda e: int(e.get("at_seq", 0)))
if not events:
    raise SystemExit(0)
last = events[-1]
messages = {m.get("id"): m for m in collab.get("messages", [])}
assignments = {a.get("id"): a for a in collab.get("assignments", [])}
msg = messages.get(last.get("message_ref"), {})
assignment_ref = msg.get("assignment_ref")
assignment = assignments.get(assignment_ref, {})
checkbox = assignment.get("checkbox_ref")
actor = last.get("actor_agent_ref")
to_status = last.get("to_status")
subject = f"governance/collab: sync {assignment_ref} -> {to_status}"
if checkbox:
    subject = f"governance/collab: sync {checkbox} ({assignment_ref}) -> {to_status}"
print(subject)
print(f"MessageRef: {last.get('message_ref')}")
print(f"MessageEvent: {last.get('id')}")
if actor:
    print(f"Actor: {actor}")
PY
  )"
  if [[ -n "${_derived}" ]]; then
    readarray -t _dlines <<<"${_derived}"
    if [[ "${SUBJECT_EXPLICIT}" -eq 0 ]]; then
      SUBJECT="${_dlines[0]}"
    fi
    # If body was not explicitly provided, use derived metadata lines.
    if [[ ${#BODY[@]} -eq 0 ]]; then
      BODY=()
      for ((i=1; i<${#_dlines[@]}; i++)); do
        BODY+=("${_dlines[$i]}")
      done
    fi
  fi
fi

if [[ "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

./control-plane/scripts/collab_validate.sh >/dev/null

staged=()
if [[ -f control-plane/collaboration/collab-model.yaml ]]; then
  staged+=("control-plane/collaboration/collab-model.yaml")
fi

while IFS= read -r f; do
  staged+=("$f")
done < <(git ls-files 'control-plane/views/*.generated.*')

if [[ ${#staged[@]} -eq 0 ]]; then
  echo "no collab/view files configured for staging" >&2
  exit 1
fi

git add "${staged[@]}"

if git diff --cached --quiet; then
  echo "nothing to commit (collab model/views unchanged)"
  exit 0
fi

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would commit with subject:"
  echo "  ${SUBJECT}"
  echo "dry-run: staged files:"
  git diff --cached --name-only
  exit 0
fi

cmd=(git commit -m "${SUBJECT}")
for line in "${BODY[@]}"; do
  cmd+=(-m "${line}")
done
if [[ "${EDIT_BODY}" -eq 1 ]]; then
  cmd+=(-e)
fi
"${cmd[@]}"
