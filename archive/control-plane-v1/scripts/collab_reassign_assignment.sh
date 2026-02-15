#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
COLLAB_PATH="${ROOT_DIR}/control-plane/collaboration/collab-model.yaml"

ASSIGNMENT_REF=""
TO_AGENT_REF=""
FROM_AGENT_REF="AGENT_MAIN"
NEW_ASSIGNMENT_ID=""
BRANCH_OVERRIDE=""
COMMIT_SHA=""
NO_REFRESH=0
DRY_RUN=0
PAYLOAD_REFS=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_reassign_assignment.sh \
    --assignment-ref ASSIGN_... \
    --to-agent-ref AGENT_... \
    [options]

Options:
  --from-agent-ref <id>      Reassignment actor (default: AGENT_MAIN).
  --new-assignment-id <id>   Optional explicit replacement assignment id.
  --branch <name>            Optional explicit replacement branch.
  --payload-ref <path>       Replacement payload refs (repeatable); defaults to source message payloads.
  --commit <sha>             Commit to bind on emitted events (default: current HEAD short).
  --no-refresh               Do not regenerate views after update.
  --dry-run                  Print plan only.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --assignment-ref) ASSIGNMENT_REF="${2:-}"; shift 2 ;;
    --to-agent-ref) TO_AGENT_REF="${2:-}"; shift 2 ;;
    --from-agent-ref) FROM_AGENT_REF="${2:-}"; shift 2 ;;
    --new-assignment-id) NEW_ASSIGNMENT_ID="${2:-}"; shift 2 ;;
    --branch) BRANCH_OVERRIDE="${2:-}"; shift 2 ;;
    --payload-ref) PAYLOAD_REFS+=("${2:-}"); shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${ASSIGNMENT_REF}" || -z "${TO_AGENT_REF}" ]]; then
  echo "--assignment-ref and --to-agent-ref are required" >&2
  usage >&2
  exit 1
fi

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

plan_json="$(
python3 - "$COLLAB_PATH" "$ASSIGNMENT_REF" "$TO_AGENT_REF" "$NEW_ASSIGNMENT_ID" "$BRANCH_OVERRIDE" "${PAYLOAD_REFS[@]}" <<'PY'
import json
import re
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
assignment_ref = sys.argv[2]
to_agent_ref = sys.argv[3]
new_assignment_id_arg = sys.argv[4]
branch_override = sys.argv[5]
payload_override = [x for x in sys.argv[6:] if x]

agents = {a.get("id"): a for a in collab.get("agents", [])}
if to_agent_ref not in agents:
    raise SystemExit(f"unknown to-agent-ref: {to_agent_ref}")

assignments = {a.get("id"): a for a in collab.get("assignments", [])}
if assignment_ref not in assignments:
    raise SystemExit(f"unknown assignment-ref: {assignment_ref}")
assignment = assignments[assignment_ref]

messages = [m for m in collab.get("messages", []) if m.get("assignment_ref") == assignment_ref]
if not messages:
    raise SystemExit(f"assignment has no messages: {assignment_ref}")

by_mid = {}
for e in collab.get("message_events", []):
    by_mid.setdefault(e.get("message_ref"), []).append(e)

def current_status(msg):
    evs = sorted(by_mid.get(msg.get("id"), []), key=lambda e: int(e.get("at_seq", 0)))
    return (evs[-1].get("to_status") if evs else msg.get("initial_status"))

open_status = {"queued", "sent", "acknowledged", "fulfilled", "ingested"}
active_msgs = [m for m in messages if current_status(m) in open_status]
if len(active_msgs) != 1:
    raise SystemExit(
        f"assignment must have exactly one open message for reassignment, got={len(active_msgs)}"
    )
msg = active_msgs[0]
cur = current_status(msg)
if cur not in {"queued", "sent", "acknowledged"}:
    raise SystemExit(f"message status {cur} not eligible for reassignment (expected queued/sent/acknowledged)")

checkbox_ref = assignment.get("checkbox_ref")
if not isinstance(checkbox_ref, str) or not re.fullmatch(r"[A-Z]{1,2}[0-9]+\.[0-9]+", checkbox_ref):
    raise SystemExit(f"invalid assignment checkbox_ref: {checkbox_ref}")

# Prefer phase extraction from assignment id lane.
aid_match = re.fullmatch(r"ASSIGN_PHASE([0-9]+)_[A-Z0-9_]+", assignment_ref)
if aid_match:
    phase_no = int(aid_match.group(1))
else:
    # Fallback for legacy assignment ids.
    phase_match = re.fullmatch(r"[A-Z]{1,2}([0-9]+)\.[0-9]+", checkbox_ref)
    if not phase_match:
        raise SystemExit(f"cannot derive phase number from assignment_ref/checkbox_ref: {assignment_ref} / {checkbox_ref}")
    phase_no = int(phase_match.group(1))
cb_token = checkbox_ref.replace(".", "")
agent_tag = re.sub(r"^AGENT_", "", to_agent_ref).upper()

existing_assign_ids = {a.get("id") for a in collab.get("assignments", [])}
if new_assignment_id_arg:
    new_assignment_id = new_assignment_id_arg
    if new_assignment_id in existing_assign_ids:
        raise SystemExit(f"new assignment id already exists: {new_assignment_id}")
else:
    i = 1
    while True:
        cand = f"ASSIGN_PHASE{phase_no:02d}_{cb_token}_{agent_tag}_I{i:02d}"
        if cand not in existing_assign_ids:
            new_assignment_id = cand
            break
        i += 1

if branch_override:
    new_branch = branch_override
else:
    i = int(new_assignment_id.rsplit("_I", 1)[-1])
    new_branch = f"phase{phase_no}.{checkbox_ref.lower()}.i{i:02d}"

payload_refs = payload_override if payload_override else list(msg.get("payload_refs", []))
if not payload_refs:
    payload_refs = ["AGENTS.md", "control-plane/README.md"]

print(json.dumps({
    "source_assignment_ref": assignment_ref,
    "source_message_ref": msg.get("id"),
    "source_status": cur,
    "checkbox_ref": checkbox_ref,
    "new_assignment_id": new_assignment_id,
    "new_branch": new_branch,
    "payload_refs": payload_refs,
}))
PY
)"

src_message_ref="$(printf '%s' "${plan_json}" | python3 -c 'import json,sys;print(json.load(sys.stdin)["source_message_ref"])')"
src_status="$(printf '%s' "${plan_json}" | python3 -c 'import json,sys;print(json.load(sys.stdin)["source_status"])')"
checkbox_ref="$(printf '%s' "${plan_json}" | python3 -c 'import json,sys;print(json.load(sys.stdin)["checkbox_ref"])')"
new_assignment_id="$(printf '%s' "${plan_json}" | python3 -c 'import json,sys;print(json.load(sys.stdin)["new_assignment_id"])')"
new_branch="$(printf '%s' "${plan_json}" | python3 -c 'import json,sys;print(json.load(sys.stdin)["new_branch"])')"

readarray -t payload_refs < <(printf '%s' "${plan_json}" | python3 -c 'import json,sys; [print(x) for x in json.load(sys.stdin)["payload_refs"]]')

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run reassignment plan:"
  echo "source assignment: ${ASSIGNMENT_REF}"
  echo "source message: ${src_message_ref} (${src_status})"
  echo "target agent: ${TO_AGENT_REF}"
  echo "new assignment: ${new_assignment_id}"
  echo "new branch: ${new_branch}"
  echo "checkbox: ${checkbox_ref}"
  echo "payload refs:"
  printf ' - %s\n' "${payload_refs[@]}"
  exit 0
fi

# 1) Terminalize source message using legal transitions.
if [[ "${src_status}" == "acknowledged" ]]; then
  ./control-plane/scripts/collab_append_event.sh \
    --message-ref "${src_message_ref}" \
    --to-status sent \
    --actor-agent-ref "${FROM_AGENT_REF}" \
    --commit "${COMMIT_SHA}" \
    --notes "Reassignment handoff: acknowledged->sent before rescind to ${TO_AGENT_REF}" \
    --skip-validate \
    --no-refresh
fi

./control-plane/scripts/collab_append_event.sh \
  --message-ref "${src_message_ref}" \
  --to-status rescinded \
  --actor-agent-ref "${FROM_AGENT_REF}" \
  --commit "${COMMIT_SHA}" \
  --rescinded-reason "Reassigned to ${TO_AGENT_REF}" \
  --notes "Rescinded during reassignment to ${TO_AGENT_REF}" \
  --skip-validate \
  --no-refresh

# 2) Mark source assignment terminal (blocked) to free checkbox lane.
python3 - "$COLLAB_PATH" "$ASSIGNMENT_REF" "$TO_AGENT_REF" <<'PY'
import sys
from pathlib import Path
import yaml

path = Path(sys.argv[1])
assignment_ref = sys.argv[2]
to_agent_ref = sys.argv[3]
data = yaml.safe_load(path.read_text(encoding="utf-8"))
found = False
for a in data.get("assignments", []):
    if a.get("id") == assignment_ref:
        found = True
        a["status"] = "done"
        a["outcome"] = "blocked"
        note = a.get("notes", "")
        suffix = f"Reassigned to {to_agent_ref}."
        a["notes"] = f"{note} | {suffix}" if note and suffix not in note else (note or suffix)
        break
if not found:
    raise SystemExit(f"assignment not found: {assignment_ref}")
path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
PY

./control-plane/scripts/collab_validate.sh >/dev/null

# 3) Create replacement assignment+dispatch packet.
create_cmd=(
  ./control-plane/scripts/collab_create_assignment.sh
  --assignment-id "${new_assignment_id}"
  --agent-ref "${TO_AGENT_REF}"
  --checkbox-ref "${checkbox_ref}"
  --branch "${new_branch}"
  --from-agent-ref "${FROM_AGENT_REF}"
  --commit "${COMMIT_SHA}"
  --assignment-notes "Reassigned from ${ASSIGNMENT_REF}"
  --dispatch-notes "Reassignment dispatch from ${ASSIGNMENT_REF}"
  --no-refresh
)
for p in "${payload_refs[@]}"; do
  create_cmd+=(--payload-ref "${p}")
done
"${create_cmd[@]}"

if [[ "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

./control-plane/scripts/collab_validate.sh >/dev/null
echo "reassigned ${ASSIGNMENT_REF} -> ${new_assignment_id} (${TO_AGENT_REF})"
