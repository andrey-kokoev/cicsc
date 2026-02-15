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
PLAN_ONLY=0
APPLY_RUN=""
RESUME_RUN=""
RUN_ID=""
JOURNAL_DIR="control-plane/logs/dispatch-runs"
PAYLOAD_REFS=()
CHECKBOX_REFS=()
EXCLUDE_CHECKBOX_REFS=()
PHASE_FILTER=""
MILESTONE_FILTER=""
STRATEGY="fifo"
SUBJECT=""
BODY=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_dispatch_batch.sh [--agent-ref AGENT_...] [options]

Plan selection:
  --count <n>                 Number of checkboxes to select when auto-planning (default: 1).
  --checkbox-ref <id>         Explicit checkbox ref (repeatable); bypasses auto-selection.
  --exclude-checkbox <id>     Exclude checkbox from auto-selection (repeatable).
  --phase <n|Pnn>             Restrict auto-selection to a phase (e.g. 35 or P35).
  --milestone <id>            Restrict auto-selection to a milestone (e.g. AZ2).
  --strategy <fifo|lifo>      Ordering strategy for auto-selection (default: fifo).

Dispatch context (for new plan/apply):
  --payload-ref <path>        Payload ref for each dispatch (repeatable).
  --from-agent-ref <id>       Dispatching agent (default: AGENT_MAIN).
  --initial-status <s>        queued|sent (default: sent).
  --commit <sha>              Event commit sha (default: current HEAD short).

Run lifecycle:
  --run-id <id>               Explicit run id for new plan file.
  --plan-only                 Create run plan file only; do not apply.
  --apply-run <id|path>       Apply an existing run file.
  --resume <id|path>          Apply pending/failed rows from an existing run file.
  --journal-dir <path>        Run journal directory (default: control-plane/logs/dispatch-runs).

Commit control:
  --subject <text>            Commit subject override.
  --body <text>               Commit body line (repeatable).
  --no-commit                 Do not commit after successful apply.
  --dry-run                   Resolve plan and validate IDs without writing.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --agent-ref) AGENT_REF="${2:-}"; shift 2 ;;
    --count) COUNT="${2:-}"; shift 2 ;;
    --checkbox-ref) CHECKBOX_REFS+=("${2:-}"); shift 2 ;;
    --exclude-checkbox) EXCLUDE_CHECKBOX_REFS+=("${2:-}"); shift 2 ;;
    --phase) PHASE_FILTER="${2:-}"; shift 2 ;;
    --milestone) MILESTONE_FILTER="${2:-}"; shift 2 ;;
    --strategy) STRATEGY="${2:-}"; shift 2 ;;
    --payload-ref) PAYLOAD_REFS+=("${2:-}"); shift 2 ;;
    --from-agent-ref) FROM_AGENT_REF="${2:-}"; shift 2 ;;
    --initial-status) INITIAL_STATUS="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --run-id) RUN_ID="${2:-}"; shift 2 ;;
    --plan-only) PLAN_ONLY=1; shift ;;
    --apply-run) APPLY_RUN="${2:-}"; shift 2 ;;
    --resume) RESUME_RUN="${2:-}"; shift 2 ;;
    --journal-dir) JOURNAL_DIR="${2:-}"; shift 2 ;;
    --subject) SUBJECT="${2:-}"; shift 2 ;;
    --body) BODY+=("${2:-}"); shift 2 ;;
    --no-commit) NO_COMMIT=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "${COUNT}" =~ ^[0-9]+$ ]] || [[ "${COUNT}" -lt 1 ]]; then
  echo "--count must be a positive integer" >&2
  exit 1
fi
if [[ "${INITIAL_STATUS}" != "queued" && "${INITIAL_STATUS}" != "sent" ]]; then
  echo "--initial-status must be queued or sent" >&2
  exit 1
fi
if [[ "${STRATEGY}" != "fifo" && "${STRATEGY}" != "lifo" ]]; then
  echo "--strategy must be fifo or lifo" >&2
  exit 1
fi

mode_count=0
[[ -n "${APPLY_RUN}" ]] && mode_count=$((mode_count+1))
[[ -n "${RESUME_RUN}" ]] && mode_count=$((mode_count+1))
if [[ "${mode_count}" -gt 1 ]]; then
  echo "--apply-run and --resume are mutually exclusive" >&2
  exit 1
fi

if [[ ${#PAYLOAD_REFS[@]} -eq 0 ]]; then
  PAYLOAD_REFS=("AGENTS.md" "control-plane/README.md")
fi

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

# In commit mode, require a clean starting point before creating run journals or applying.
if [[ "${NO_COMMIT}" -eq 0 && "${DRY_RUN}" -eq 0 && "${PLAN_ONLY}" -eq 0 ]]; then
  # Only block when canonical collab/view files are already dirty.
  if [[ -n "$(git status --porcelain -- control-plane/collaboration/collab-model.yaml control-plane/views)" ]]; then
    echo "batch apply with commit requires clean collab model/views before dispatch starts (unrelated dirty files are allowed)" >&2
    exit 1
  fi
fi

mkdir -p "${JOURNAL_DIR}"

normalize_phase_filter() {
  local v="$1"
  if [[ -z "${v}" ]]; then
    echo ""
    return
  fi
  if [[ "${v}" =~ ^[Pp]([0-9]+)$ ]]; then
    echo "${BASH_REMATCH[1]}"
  elif [[ "${v}" =~ ^[0-9]+$ ]]; then
    echo "${v}"
  else
    echo "invalid --phase value: ${v}" >&2
    exit 1
  fi
}

phase_num_filter="$(normalize_phase_filter "${PHASE_FILTER}")"

resolve_run_file_path() {
  local run_ref="$1"
  if [[ -z "${run_ref}" ]]; then
    echo ""
    return
  fi
  if [[ "${run_ref}" == */* || "${run_ref}" == *.json ]]; then
    echo "${run_ref}"
    return
  fi
  echo "${JOURNAL_DIR%/}/${run_ref}.json"
}

load_run_defaults() {
  local run_path="$1"
  python3 - "$run_path" "$AGENT_REF" "$FROM_AGENT_REF" "$INITIAL_STATUS" "$COMMIT_SHA" <<'PY'
import json
import sys
from pathlib import Path

doc = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
agent_ref = sys.argv[2]
from_agent_ref = sys.argv[3]
initial_status = sys.argv[4]
commit_sha = sys.argv[5]

if not agent_ref:
    agent_ref = doc.get("agent_ref", "")
if not from_agent_ref or from_agent_ref == "AGENT_MAIN":
    from_agent_ref = doc.get("from_agent_ref", from_agent_ref)
if not initial_status or initial_status == "sent":
    initial_status = doc.get("initial_status", initial_status)
if not commit_sha:
    commit_sha = doc.get("commit", "")

print(agent_ref)
print(from_agent_ref)
print(initial_status)
print(commit_sha)
PY
}

write_plan_file() {
  local run_path="$1"
  local rows_json="$2"
  python3 - "$run_path" "$rows_json" "$AGENT_REF" "$FROM_AGENT_REF" "$INITIAL_STATUS" "$COMMIT_SHA" "$phase_num_filter" "$MILESTONE_FILTER" "$STRATEGY" "$COUNT" <<'PY'
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path

run_path = Path(sys.argv[1])
rows = json.loads(sys.argv[2])
agent_ref = sys.argv[3]
from_agent_ref = sys.argv[4]
initial_status = sys.argv[5]
commit_sha = sys.argv[6]
phase_filter = sys.argv[7]
milestone_filter = sys.argv[8]
strategy = sys.argv[9]
count = int(sys.argv[10])

doc = {
    "run_id": run_path.stem,
    "created_at": datetime.now(timezone.utc).isoformat(),
    "agent_ref": agent_ref,
    "from_agent_ref": from_agent_ref,
    "initial_status": initial_status,
    "commit": commit_sha,
    "filters": {
        "phase_number": int(phase_filter) if phase_filter else None,
        "milestone_id": milestone_filter or None,
        "strategy": strategy,
        "count": len(rows),
        "requested_count": count,
    },
    "rows": rows,
}
run_path.parent.mkdir(parents=True, exist_ok=True)
run_path.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
print(str(run_path))
PY
}

build_rows_json() {
  python3 - "$ROOT_DIR/control-plane/execution/execution-ledger.yaml" "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$AGENT_REF" "$COUNT" "$COMMIT_SHA" "$phase_num_filter" "$MILESTONE_FILTER" "$STRATEGY" "${CHECKBOX_REFS[@]}" -- "${EXCLUDE_CHECKBOX_REFS[@]}" <<'PY'
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
phase_filter = sys.argv[6]
milestone_filter = sys.argv[7]
strategy = sys.argv[8]
args = sys.argv[9:]
sep = args.index("--") if "--" in args else len(args)
explicit = [x for x in args[:sep] if x]
excluded = set(x for x in args[sep+1:] if x)

agents = {a.get("id"): a for a in collab.get("agents", [])}
if agent_ref not in agents:
    raise SystemExit(f"unknown agent_ref: {agent_ref}")

gov = collab.get("worktree_governance", {})
if gov.get("enforce_main_dispatch_authority"):
    expected = gov.get("main_dispatch_authority_agent_ref")
    # Dispatcher validates at runtime too; include in plan metadata via each row.

active_statuses = {"assigned", "in_progress", "submitted"}
assigned = {
    a.get("checkbox_ref")
    for a in collab.get("assignments", [])
    if a.get("status") in active_statuses
}
existing_assign_ids = {a.get("id") for a in collab.get("assignments", [])}
existing_msg_ids = {m.get("id") for m in collab.get("messages", [])}

rows_all = []
order = 0
for ph in exe.get("phases", []):
    pnum = ph.get("number")
    pid = ph.get("id")
    if phase_filter and str(pnum) != str(phase_filter):
        continue
    for ms in ph.get("milestones", []):
        mid = ms.get("id")
        if milestone_filter and mid != milestone_filter:
            continue
        for cb in ms.get("checkboxes", []):
            cid = cb.get("id")
            order += 1
            rows_all.append({
                "order": order,
                "phase_id": pid,
                "phase_number": int(pnum),
                "milestone_id": mid,
                "checkbox_ref": cid,
                "checkbox_title": cb.get("title", ""),
                "status": cb.get("status"),
            })

meta = {r["checkbox_ref"]: r for r in rows_all}

if explicit:
    selected = []
    for cid in explicit:
        if cid in excluded:
            continue
        if cid not in meta:
            raise SystemExit(f"unknown checkbox_ref in execution ledger: {cid}")
        r = meta[cid]
        if r["status"] != "open":
            raise SystemExit(f"checkbox not open: {cid}")
        if cid in assigned:
            raise SystemExit(f"checkbox already assigned: {cid}")
        selected.append(r)
else:
    candidates = []
    for r in rows_all:
        cid = r["checkbox_ref"]
        if cid in excluded:
            continue
        if r["status"] != "open":
            continue
        if cid in assigned:
            continue
        candidates.append(r)
    if strategy == "lifo":
        candidates = list(reversed(candidates))
    selected = candidates[:count]
    if len(selected) < count:
        raise SystemExit(f"insufficient eligible checkboxes: requested={count} got={len(selected)}")

agent_tag = re.sub(r"^AGENT_", "", agent_ref).upper()

def mk_branch(phase_number: int, checkbox_ref: str, instance_no: int) -> str:
    # Each dispatch instance gets an explicit branch suffix to avoid lane ambiguity.
    return f"phase{int(phase_number)}.{checkbox_ref.lower()}.i{instance_no:02d}"

def next_instance_number(phase_number: int, cb_token: str, agent_tag: str, existing: set[str]) -> int:
    i = 1
    while True:
        cand = f"ASSIGN_PHASE{phase_number:02d}_{cb_token}_{agent_tag}_I{i:02d}"
        if cand not in existing:
            return i
        i += 1

rows = []
for item in selected:
    cb = item["checkbox_ref"]
    pnum = int(item["phase_number"])
    cb_token = cb.replace(".", "")
    instance_no = next_instance_number(pnum, cb_token, agent_tag, existing_assign_ids)
    aid = f"ASSIGN_PHASE{pnum:02d}_{cb_token}_{agent_tag}_I{instance_no:02d}"
    existing_assign_ids.add(aid)

    mid = f"MSG_{aid.removeprefix('ASSIGN_')}_DISPATCH"
    if mid in existing_msg_ids:
        j = 2
        while f"{mid}_{j}" in existing_msg_ids:
            j += 1
        mid = f"{mid}_{j}"
    existing_msg_ids.add(mid)

    rows.append({
        "state": "planned",
        "error": "",
        "assignment_id": aid,
        "message_id": mid,
        "checkbox_ref": cb,
        "phase_number": pnum,
        "instance_no": instance_no,
        "milestone_id": item["milestone_id"],
        "title": item["checkbox_title"],
        "branch": mk_branch(pnum, cb, instance_no),
        "commit": commit_sha,
    })

print(json.dumps(rows))
PY
}

update_run_row_state() {
  local run_path="$1"
  local idx="$2"
  local state="$3"
  local error="$4"
  python3 - "$run_path" "$idx" "$state" "$error" <<'PY'
import json
import sys
from pathlib import Path
p = Path(sys.argv[1])
idx = int(sys.argv[2])
state = sys.argv[3]
err = sys.argv[4]
doc = json.loads(p.read_text(encoding="utf-8"))
rows = doc.get("rows", [])
if idx < 0 or idx >= len(rows):
    raise SystemExit(f"row index out of range: {idx}")
rows[idx]["state"] = state
rows[idx]["error"] = err
p.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
PY
}

ensure_dispatch_authority() {
  python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$FROM_AGENT_REF" <<'PY'
import sys
from pathlib import Path
import yaml
collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
from_agent = sys.argv[2]
agents = {a.get("id") for a in collab.get("agents", [])}
if from_agent not in agents:
    raise SystemExit(f"unknown from-agent-ref: {from_agent}")
gov = collab.get("worktree_governance", {})
if gov.get("enforce_main_dispatch_authority"):
    expected = gov.get("main_dispatch_authority_agent_ref")
    if from_agent != expected:
        raise SystemExit(
            f"dispatch authority denied: enforce_main_dispatch_authority=true expects {expected}, got {from_agent}"
        )
PY
}

apply_run_file() {
  local run_path="$1"
  local only_pending="$2"

  mapfile -t rows < <(python3 - "$run_path" "$only_pending" <<'PY'
import json, sys
from pathlib import Path
p = Path(sys.argv[1])
only_pending = sys.argv[2] == "1"
doc = json.loads(p.read_text(encoding="utf-8"))
for i, r in enumerate(doc.get("rows", [])):
    state = r.get("state", "planned")
    if only_pending and state == "applied":
        continue
    print("\t".join([
      str(i), r.get("assignment_id", ""), r.get("checkbox_ref", ""), r.get("branch", ""),
      r.get("message_id", ""), r.get("title", ""), r.get("commit", ""), state, str(r.get("instance_no", 1))
    ]))
PY
)

  local applied=0
  local failed=0
  row_already_applied() {
    local assignment_id="$1"
    local message_id="$2"
    python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$assignment_id" "$message_id" <<'PY'
import sys
from pathlib import Path
import yaml

doc = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
aid = sys.argv[2]
mid = sys.argv[3]
assignments = {a.get("id") for a in doc.get("assignments", [])}
messages = {m.get("id"): m for m in doc.get("messages", [])}
if aid not in assignments:
    print("0")
    raise SystemExit(0)
if mid not in messages:
    print("0")
    raise SystemExit(0)
events = [e for e in doc.get("message_events", []) if e.get("message_ref") == mid]
if not events:
    print("0")
    raise SystemExit(0)
print("1")
PY
  }
  for line in "${rows[@]}"; do
    IFS=$'\t' read -r idx assignment_id checkbox_ref branch message_id title row_commit row_state row_instance <<<"${line}"
    row_instance="$(printf '%02d' "${row_instance:-1}")"

    if [[ "${row_state}" == "applied" ]]; then
      continue
    fi

    if [[ "$(row_already_applied "${assignment_id}" "${message_id}")" == "1" ]]; then
      update_run_row_state "${run_path}" "${idx}" "applied" ""
      applied=$((applied + 1))
      continue
    fi

    create_cmd=(
      ./control-plane/scripts/collab_create_assignment.sh
      --assignment-id "${assignment_id}"
      --agent-ref "${AGENT_REF}"
      --checkbox-ref "${checkbox_ref}"
      --branch "${branch}"
      --from-agent-ref "${FROM_AGENT_REF}"
      --initial-status "${INITIAL_STATUS}"
      --commit "${row_commit}"
      --message-id "${message_id}"
      --assignment-notes "Dispatch instance i${row_instance} for ${checkbox_ref}: ${title}"
      --dispatch-notes "Dispatch instance i${row_instance} ${checkbox_ref} -> ${AGENT_REF} via collab_dispatch_batch.sh"
      --no-refresh
    )
    for p in "${PAYLOAD_REFS[@]}"; do
      create_cmd+=(--payload-ref "${p}")
    done

    if output="$("${create_cmd[@]}" 2>&1)"; then
      update_run_row_state "${run_path}" "${idx}" "applied" ""
      applied=$((applied + 1))
    else
      update_run_row_state "${run_path}" "${idx}" "failed" "${output//$'\n'/ | }"
      echo "dispatch failed for row ${idx} (${checkbox_ref}): ${output}" >&2
      failed=$((failed + 1))
    fi
  done

  echo "${applied}:${failed}"
}

run_path=""
if [[ -n "${APPLY_RUN}" || -n "${RESUME_RUN}" ]]; then
  run_ref="${APPLY_RUN:-$RESUME_RUN}"
  run_path="$(resolve_run_file_path "${run_ref}")"
  if [[ ! -f "${run_path}" ]]; then
    echo "run file not found: ${run_path}" >&2
    exit 1
  fi
  readarray -t _defaults < <(load_run_defaults "${run_path}")
  AGENT_REF="${_defaults[0]}"
  FROM_AGENT_REF="${_defaults[1]}"
  INITIAL_STATUS="${_defaults[2]}"
  if [[ -z "${COMMIT_SHA}" ]]; then
    COMMIT_SHA="${_defaults[3]}"
  fi
else
  if [[ -z "${AGENT_REF}" ]]; then
    echo "--agent-ref is required (or provide --apply-run/--resume with run metadata)" >&2
    exit 1
  fi
  if [[ -z "${COMMIT_SHA}" ]]; then
    COMMIT_SHA="$(git rev-parse --short HEAD)"
  fi
  rows_json="$(build_rows_json)"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "dry-run dispatch plan:"
    python3 - "$rows_json" <<'PY'
import json,sys
print(json.dumps(json.loads(sys.argv[1]), indent=2))
PY
    exit 0
  fi
  if [[ -z "${RUN_ID}" ]]; then
    RUN_ID="dispatch-run-$(date -u +%Y%m%dT%H%M%SZ)"
  fi
  run_path="${JOURNAL_DIR%/}/${RUN_ID}.json"
  if [[ -f "${run_path}" ]]; then
    echo "run file already exists: ${run_path}" >&2
    exit 1
  fi
  run_path="$(write_plan_file "${run_path}" "${rows_json}")"
  echo "dispatch plan written: ${run_path}"
  if [[ "${PLAN_ONLY}" -eq 1 ]]; then
    exit 0
  fi
fi

if [[ -z "${AGENT_REF}" ]]; then
  echo "could not resolve agent_ref from arguments or run metadata" >&2
  exit 1
fi
if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

ensure_dispatch_authority

only_pending=0
[[ -n "${RESUME_RUN}" ]] && only_pending=1
result="$(apply_run_file "${run_path}" "${only_pending}")"
applied_count="${result%%:*}"
failed_count="${result##*:}"

if [[ "${applied_count}" -gt 0 ]]; then
  ./control-plane/scripts/collab_sync.sh >/dev/null
fi

if [[ "${NO_COMMIT}" -eq 0 && "${applied_count}" -gt 0 ]]; then
  # Include run journal in the same atomic dispatch commit.
  if [[ -f "${run_path}" ]]; then
    git add "${run_path}"
  fi
  if [[ -z "${SUBJECT}" ]]; then
    SUBJECT="governance/collab: batch dispatch apply $(basename "${run_path}" .json)"
  fi
  commit_cmd=(./control-plane/scripts/collab_commit_views.sh --subject "${SUBJECT}" --no-refresh)
  if [[ ${#BODY[@]} -eq 0 ]]; then
    commit_cmd+=(--body "Dispatch run: ${run_path}" --body "Applied rows: ${applied_count}, Failed rows: ${failed_count}")
  else
    for b in "${BODY[@]}"; do
      commit_cmd+=(--body "${b}")
    done
  fi
  "${commit_cmd[@]}"
fi

echo "dispatch apply complete: applied=${applied_count} failed=${failed_count} run=${run_path}"
if [[ "${failed_count}" -gt 0 ]]; then
  echo "resume with: ./control-plane/scripts/collab_dispatch_batch.sh --agent-ref ${AGENT_REF} --resume ${run_path} --no-commit" >&2
  exit 1
fi
