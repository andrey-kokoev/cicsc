#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

AGENT_REF=""
COUNT=1
FROM_AGENT_REF="AGENT_MAIN"
INITIAL_STATUS="sent"
COMMIT_SHA=""
NO_COMMIT=0
DRY_RUN=0
PAYLOAD_REFS=()
CHECKBOX_REFS=()
SUBJECT=""
BODY=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_dispatch_batch.sh --agent-ref AGENT_... [options]

Options:
  --count <n>           Number of next unassigned open checkboxes to dispatch (default: 1).
  --checkbox-ref <id>   Explicit checkbox ref (repeatable); overrides --count selection.
  --payload-ref <path>  Payload ref for each dispatch (repeatable).
  --from-agent-ref <id> Dispatching agent (default: AGENT_MAIN).
  --initial-status <s>  queued|sent (default: sent).
  --commit <sha>        Event commit sha (default: current HEAD short).
  --subject <text>      Commit subject override for batch commit.
  --body <text>         Commit body line (repeatable).
  --no-commit           Do not commit after dispatching.
  --dry-run             Resolve plan and validate IDs without writing.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --agent-ref) AGENT_REF="${2:-}"; shift 2 ;;
    --count) COUNT="${2:-}"; shift 2 ;;
    --checkbox-ref) CHECKBOX_REFS+=("${2:-}"); shift 2 ;;
    --payload-ref) PAYLOAD_REFS+=("${2:-}"); shift 2 ;;
    --from-agent-ref) FROM_AGENT_REF="${2:-}"; shift 2 ;;
    --initial-status) INITIAL_STATUS="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --subject) SUBJECT="${2:-}"; shift 2 ;;
    --body) BODY+=("${2:-}"); shift 2 ;;
    --no-commit) NO_COMMIT=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${AGENT_REF}" ]]; then
  echo "--agent-ref is required" >&2
  usage >&2
  exit 1
fi
if ! [[ "${COUNT}" =~ ^[0-9]+$ ]] || [[ "${COUNT}" -lt 1 ]]; then
  echo "--count must be a positive integer" >&2
  exit 1
fi
if [[ "${INITIAL_STATUS}" != "queued" && "${INITIAL_STATUS}" != "sent" ]]; then
  echo "--initial-status must be queued or sent" >&2
  exit 1
fi
if [[ ${#PAYLOAD_REFS[@]} -eq 0 ]]; then
  PAYLOAD_REFS=("AGENTS.md" "control-plane/README.md")
fi

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

plan_json="$(
python3 - "$ROOT_DIR/control-plane/execution/execution-ledger.yaml" \
  "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" \
  "$AGENT_REF" "$COUNT" "$COMMIT_SHA" "${CHECKBOX_REFS[@]}" <<'PY'
import json
import re
import sys
from pathlib import Path
import yaml

exe = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
collab = yaml.safe_load(Path(sys.argv[2]).read_text(encoding="utf-8"))
agent_ref = sys.argv[3]
count = int(sys.argv[4])
commit_sha = sys.argv[5]
explicit = sys.argv[6:]

agents = {a.get("id"): a for a in collab.get("agents", [])}
if agent_ref not in agents:
    raise SystemExit(f"unknown agent_ref: {agent_ref}")

assigned = {a.get("checkbox_ref") for a in collab.get("assignments", [])}
existing_assign_ids = {a.get("id") for a in collab.get("assignments", [])}
existing_msg_ids = {m.get("id") for m in collab.get("messages", [])}

checkbox_meta = {}
for ph in exe.get("phases", []):
    pnum = ph.get("number")
    for ms in ph.get("milestones", []):
        for cb in ms.get("checkboxes", []):
            cid = cb.get("id")
            checkbox_meta[cid] = {
                "phase_id": ph.get("id"),
                "phase_number": pnum,
                "title": cb.get("title", ""),
                "status": cb.get("status"),
            }

if explicit:
    selected = explicit
else:
    selected = []
    for ph in exe.get("phases", []):
        for ms in ph.get("milestones", []):
            for cb in ms.get("checkboxes", []):
                cid = cb.get("id")
                if cb.get("status") != "open":
                    continue
                if cid in assigned:
                    continue
                selected.append(cid)
                if len(selected) >= count:
                    break
            if len(selected) >= count:
                break
        if len(selected) >= count:
            break

if len(selected) < (len(explicit) if explicit else count):
    raise SystemExit(f"insufficient eligible checkboxes: requested={len(explicit) if explicit else count} got={len(selected)}")

agent_tag = re.sub(r"^AGENT_", "", agent_ref).upper()

def mk_branch(phase_number: int, checkbox_ref: str) -> str:
    return f"phase{int(phase_number)}.{checkbox_ref.lower()}"

def next_unique_id(base: str, existing: set[str]) -> str:
    if base not in existing:
        return base
    i = 2
    while True:
        cand = f"{base}_{i}"
        if cand not in existing:
            return cand
        i += 1

rows = []
for idx, cb in enumerate(selected, start=1):
    meta = checkbox_meta.get(cb)
    if not meta:
        raise SystemExit(f"unknown checkbox_ref in execution ledger: {cb}")
    if meta["status"] != "open":
        raise SystemExit(f"checkbox not open: {cb}")
    pnum = int(meta["phase_number"])
    cb_token = cb.replace(".", "")
    base_assign = f"ASSIGN_PHASE{pnum:02d}_{cb_token}_{agent_tag}_BATCH"
    aid = next_unique_id(base_assign, existing_assign_ids)
    existing_assign_ids.add(aid)
    mid = f"MSG_{aid.removeprefix('ASSIGN_')}_DISPATCH"
    if mid in existing_msg_ids:
        j = 2
        while f"{mid}_{j}" in existing_msg_ids:
            j += 1
        mid = f"{mid}_{j}"
    existing_msg_ids.add(mid)
    rows.append({
        "checkbox_ref": cb,
        "phase_number": pnum,
        "assignment_id": aid,
        "message_id": mid,
        "branch": mk_branch(pnum, cb),
        "title": meta["title"],
        "commit": commit_sha,
    })

print(json.dumps({"rows": rows}, indent=2))
PY
)"

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run dispatch plan:"
  echo "${plan_json}"
  exit 0
fi

readarray -t _dispatch_lines < <(python3 - "${plan_json}" <<'PY'
import json, sys
doc = json.loads(sys.argv[1])
for r in doc["rows"]:
    print("\t".join([
        r["assignment_id"], r["checkbox_ref"], r["branch"], r["message_id"], r["title"], r["commit"]
    ]))
PY
)

for line in "${_dispatch_lines[@]}"; do
  IFS=$'\t' read -r assignment_id checkbox_ref branch message_id title commit_sha <<<"${line}"
  create_cmd=(
    ./control-plane/scripts/collab_create_assignment.sh
    --assignment-id "${assignment_id}"
    --agent-ref "${AGENT_REF}"
    --checkbox-ref "${checkbox_ref}"
    --branch "${branch}"
    --from-agent-ref "${FROM_AGENT_REF}"
    --initial-status "${INITIAL_STATUS}"
    --commit "${commit_sha}"
    --message-id "${message_id}"
    --assignment-notes "Batch dispatch for ${checkbox_ref}: ${title}"
    --dispatch-notes "Batch dispatch ${checkbox_ref} -> ${AGENT_REF} via collab_dispatch_batch.sh"
    --no-refresh
  )
  for p in "${PAYLOAD_REFS[@]}"; do
    create_cmd+=(--payload-ref "${p}")
  done
  "${create_cmd[@]}"
done

./control-plane/scripts/collab_sync.sh >/dev/null

if [[ "${NO_COMMIT}" -eq 0 ]]; then
  if [[ -z "${SUBJECT}" ]]; then
    SUBJECT="governance/collab: batch dispatch $(python3 - "${plan_json}" <<'PY'
import json,sys
d=json.loads(sys.argv[1])
print(", ".join(r["checkbox_ref"] for r in d["rows"]))
PY
)"
  fi
  commit_cmd=(./control-plane/scripts/collab_commit_views.sh --subject "${SUBJECT}" --no-refresh)
  if [[ ${#BODY[@]} -eq 0 ]]; then
    commit_cmd+=(--body "Batch dispatcher: collab_dispatch_batch.sh")
  else
    for b in "${BODY[@]}"; do
      commit_cmd+=(--body "${b}")
    done
  fi
  "${commit_cmd[@]}"
fi

echo "batch dispatch complete for ${AGENT_REF}"
echo "${plan_json}"
