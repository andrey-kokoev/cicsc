#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

ROLE=""
WORKTREE="${PWD}"
AGENT_REF=""
MAX_ITER=50
NO_COMMIT=0
DRY_RUN=0
WITH_FRICTION_TRIAGE=0
FRICTION_DECISION="accept_later"
FRICTION_NOTES=""
FRICTION_BACKLOG_REF=""

WITH_ITEMS=()
SCRIPT_REFS=()
GATE_REFS=()
THEOREM_REFS=()
DIFFLOG_REFS=()
RAW_EVIDENCE=()
LAZY=0
AUTO_REPORT=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_process_messages.sh [options]

Options:
  --role <main|worker>   Processing role. Default: auto (main in repo root, else worker).
  --worktree <path>      Target worktree mailbox (default: current $PWD).
  --agent-ref <id>       Main-role filter when closing fulfilled messages.
  --max-iterations <n>   Safety bound for loop iterations (default: 50).
  --no-commit            Do not auto-commit state transitions.
  --dry-run              Print intended actions only.
  --with-friction-triage Enable main-side triage for actionable friction requests.
  --friction-decision <accept_now|accept_later|reject>
                         Decision applied when triaging friction requests (default: accept_later).
  --friction-notes <t>   Optional notes for friction triage decisions.
  --friction-backlog-ref <id>
                         Optional backlog ref used for accept_later decisions.

Worker fulfill options (optional):
  --with <path|cmd>
  --script <path>
  --gate-report <path>
  --theorem <path>
  --diff-log <path>
  --evidence <ref|EVID_KIND>
  --lazy
  --auto-report

If omitted, worker mode auto-resolves required script/report evidence from
assignment obligation profiles.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --role) ROLE="${2:-}"; shift 2 ;;
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --agent-ref) AGENT_REF="${2:-}"; shift 2 ;;
    --max-iterations) MAX_ITER="${2:-}"; shift 2 ;;
    --no-commit) NO_COMMIT=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --with-friction-triage) WITH_FRICTION_TRIAGE=1; shift ;;
    --friction-decision) FRICTION_DECISION="${2:-}"; shift 2 ;;
    --friction-notes) FRICTION_NOTES="${2:-}"; shift 2 ;;
    --friction-backlog-ref) FRICTION_BACKLOG_REF="${2:-}"; shift 2 ;;
    --with) WITH_ITEMS+=("${2:-}"); shift 2 ;;
    --script) SCRIPT_REFS+=("${2:-}"); shift 2 ;;
    --gate-report) GATE_REFS+=("${2:-}"); shift 2 ;;
    --theorem) THEOREM_REFS+=("${2:-}"); shift 2 ;;
    --diff-log) DIFFLOG_REFS+=("${2:-}"); shift 2 ;;
    --evidence) RAW_EVIDENCE+=("${2:-}"); shift 2 ;;
    --lazy) LAZY=1; shift ;;
    --auto-report|--report-auto) AUTO_REPORT=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "${MAX_ITER}" =~ ^[0-9]+$ ]] || [[ "${MAX_ITER}" -lt 1 ]]; then
  echo "--max-iterations must be a positive integer" >&2
  exit 1
fi
if [[ "${FRICTION_DECISION}" != "accept_now" && "${FRICTION_DECISION}" != "accept_later" && "${FRICTION_DECISION}" != "reject" ]]; then
  echo "--friction-decision must be accept_now, accept_later, or reject" >&2
  exit 1
fi

cd "${ROOT_DIR}"

if [[ -z "${ROLE}" ]]; then
  if [[ "${WORKTREE}" == "/home/andrey/src/cicsc" ]]; then
    ROLE="main"
  else
    ROLE="worker"
  fi
fi
if [[ "${ROLE}" != "main" && "${ROLE}" != "worker" ]]; then
  echo "--role must be main or worker" >&2
  exit 1
fi

if [[ "${ROLE}" == "main" ]]; then
  close_filters=()
  main_args=()
  if [[ -n "${AGENT_REF}" ]]; then
    main_args+=(--agent-ref "${AGENT_REF}")
    close_filters+=(--agent-ref "${AGENT_REF}")
  fi
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status fulfilled --count 0 --dry-run --silent-empty
    ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status ingested --count 0 --dry-run --silent-empty
    if [[ "${WITH_FRICTION_TRIAGE}" -eq 1 ]]; then
      python3 - "$ROOT_DIR/control-plane/views/worktree-mailboxes.generated.json" <<'PY'
import json,sys
doc=json.load(open(sys.argv[1], encoding="utf-8"))
mb=doc.get("mailboxes",{}).get("/home/andrey/src/cicsc",{})
inbox=mb.get("inbox",[])
rows=[m for m in inbox if m.get("kind_ref")=="MSGK_FRICTION_REQUEST" and m.get("current_status") in {"queued","sent"}]
for r in sorted(rows, key=lambda m: m.get("id","")):
    print(r.get("id",""))
PY
    fi
    exit 0
  fi

  loop_no_commit="${NO_COMMIT}"
  if [[ "${loop_no_commit}" -eq 0 ]]; then
    # If canonical collab/view files are dirty, degrade gracefully to no-commit mode.
    if [[ -n "$(git status --porcelain -- control-plane/collaboration/collab-model.yaml control-plane/views)" ]]; then
      echo "main process-messages: canonical collab/view files are pre-dirty, using --no-commit mode for this run" >&2
      loop_no_commit=1
    fi
  fi

  did_mutation=0
  while [[ 1 -eq 1 ]]; do
    before="$(python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "${close_filters[@]}" <<'PY'
import sys
from pathlib import Path
import yaml

doc=yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
agent_ref=""
args=sys.argv[2:]
i=0
while i < len(args):
    if args[i] == "--agent-ref" and i+1 < len(args):
        agent_ref=args[i+1]
        i += 2
    else:
        i += 1
messages={m.get("id"):m for m in doc.get("messages",[])}
events_by={}
for ev in doc.get("message_events",[]):
    events_by.setdefault(ev.get("message_ref"), []).append(ev)
def cur(mid,m):
    evs=sorted(events_by.get(mid,[]), key=lambda e:int(e.get("at_seq",0)))
    return evs[-1].get("to_status") if evs else m.get("initial_status")
rows=[]
for mid,m in messages.items():
    if agent_ref and m.get("to_agent_ref") != agent_ref:
        continue
    rows.append((mid,cur(mid,m)))
rows.sort()
print("|".join(f"{a}:{b}" for a,b in rows))
PY
)"

    if [[ "${loop_no_commit}" -eq 1 ]]; then
      ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status fulfilled --count 0 --no-commit --silent-empty
      ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status ingested --count 0 --no-commit --silent-empty
    else
      ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status fulfilled --count 0 --silent-empty
      ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status ingested --count 0 --silent-empty
    fi

    if [[ "${WITH_FRICTION_TRIAGE}" -eq 1 ]]; then
      mapfile -t _friction_msgs < <(python3 - "$ROOT_DIR/control-plane/views/worktree-mailboxes.generated.json" "${AGENT_REF}" <<'PY'
import json,sys
doc=json.load(open(sys.argv[1], encoding="utf-8"))
agent_ref=sys.argv[2]
mb=doc.get("mailboxes",{}).get("/home/andrey/src/cicsc",{})
inbox=mb.get("inbox",[])
rows=[]
for m in inbox:
    if m.get("kind_ref") != "MSGK_FRICTION_REQUEST":
        continue
    if m.get("current_status") not in {"queued","sent"}:
        continue
    if agent_ref and m.get("from_agent_ref") != agent_ref:
        continue
    rows.append(m.get("id",""))
for mid in sorted(set(x for x in rows if x)):
    print(mid)
PY
      )
      for fm in "${_friction_msgs[@]}"; do
        triage_cmd=(./control-plane/scripts/collab_triage_friction.sh --message-ref "${fm}" --decision "${FRICTION_DECISION}" --no-refresh)
        [[ -n "${FRICTION_NOTES}" ]] && triage_cmd+=(--notes "${FRICTION_NOTES}")
        if [[ -n "${FRICTION_BACKLOG_REF}" ]]; then
          triage_cmd+=(--backlog-ref "${FRICTION_BACKLOG_REF}")
        fi
        if [[ "${loop_no_commit}" -eq 1 ]]; then
          triage_cmd+=(--no-refresh)
        fi
        "${triage_cmd[@]}"
      done
    fi

    ./control-plane/scripts/generate_views.sh >/dev/null
    ./control-plane/scripts/collab_validate.sh >/dev/null

    after="$(python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "${close_filters[@]}" <<'PY'
import sys
from pathlib import Path
import yaml

doc=yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
agent_ref=""
args=sys.argv[2:]
i=0
while i < len(args):
    if args[i] == "--agent-ref" and i+1 < len(args):
        agent_ref=args[i+1]
        i += 2
    else:
        i += 1
messages={m.get("id"):m for m in doc.get("messages",[])}
events_by={}
for ev in doc.get("message_events",[]):
    events_by.setdefault(ev.get("message_ref"), []).append(ev)
def cur(mid,m):
    evs=sorted(events_by.get(mid,[]), key=lambda e:int(e.get("at_seq",0)))
    return evs[-1].get("to_status") if evs else m.get("initial_status")
rows=[]
for mid,m in messages.items():
    if agent_ref and m.get("to_agent_ref") != agent_ref:
        continue
    rows.append((mid,cur(mid,m)))
rows.sort()
print("|".join(f"{a}:{b}" for a,b in rows))
PY
)"

    if [[ "${before}" != "${after}" ]]; then
      did_mutation=1
      continue
    fi
    break
  done

  if [[ "${loop_no_commit}" -eq 1 && "${NO_COMMIT}" -eq 0 && "${did_mutation}" -eq 1 ]]; then
    ./control-plane/scripts/collab_commit_views.sh --subject "governance/collab: process main message loop" --body "Loop mode: no-commit fallback with consolidated sync commit"
  fi

  ./control-plane/scripts/collab_main_status.sh --refresh
  exit 0
fi

# worker role
needs_evidence=0
if [[ ${#WITH_ITEMS[@]} -gt 0 || ${#SCRIPT_REFS[@]} -gt 0 || ${#GATE_REFS[@]} -gt 0 || ${#THEOREM_REFS[@]} -gt 0 || ${#DIFFLOG_REFS[@]} -gt 0 || ${#RAW_EVIDENCE[@]} -gt 0 ]]; then
  needs_evidence=1
fi

iter=0
while [[ "${iter}" -lt "${MAX_ITER}" ]]; do
  iter=$((iter + 1))
  status_json="$(./control-plane/scripts/collab_status.sh --worktree "${WORKTREE}" --refresh --json)"
  next_action="$(python3 - "$status_json" <<'PY'
import json,sys
print(json.loads(sys.argv[1]).get('next_action','idle'))
PY
)"

  if [[ "${next_action}" == "idle" ]]; then
    echo "process-messages(worker): idle"
    break
  fi

  if [[ "${next_action}" == "claim_next_actionable" ]]; then
    cmd=(./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE}")
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      cmd+=(--dry-run)
    elif [[ "${NO_COMMIT}" -eq 0 ]]; then
      cmd+=(--auto-commit)
    fi
    "${cmd[@]}"
    continue
  fi

  if [[ "${next_action}" == "fulfill_acknowledged_first" ]]; then
    _ids="$(python3 - "$status_json" <<'PY'
import json,sys
d=json.loads(sys.argv[1])
arr=d.get('in_progress',[])
if arr:
  print(arr[0].get('message_id',''))
  print(arr[0].get('assignment_ref',''))
else:
  print("")
  print("")
PY
)"
    readarray -t _id_lines <<<"${_ids}"
    msg_ref="${_id_lines[0]:-}"
    assignment_ref="${_id_lines[1]:-}"
    if [[ -z "${msg_ref}" || -z "${assignment_ref}" ]]; then
      echo "worker process-messages: missing acknowledged message_ref" >&2
      exit 1
    fi

    resolved_with=()
    resolved_gate=""
    resolved_theorem=()
    resolved_diff=()
    if [[ "${needs_evidence}" -eq 0 ]]; then
      _resolved="$(python3 - "$assignment_ref" <<'PY'
import json
import subprocess
import sys

assignment_ref = sys.argv[1]
p = subprocess.run(
    ["./control-plane/scripts/collab_show_assignment.sh", "--ref", assignment_ref, "--json"],
    check=True,
    capture_output=True,
    text=True,
)
doc = json.loads(p.stdout)
cand = doc.get("candidate_evidence", {})
reqs = doc.get("requirements", [])
required = {r.get("evidence_kind_ref") for r in reqs if int(r.get("missing", 0)) > 0}
if not required:
    required = {"EVID_SCRIPT", "EVID_GATE_REPORT"}

def pick_best(kind):
    rows = cand.get(kind, [])
    if not rows:
        return ""
    rows = sorted(rows, key=lambda r: (0 if r.get("freshness") == "fresh" else 1, int(r.get("age_seconds", 10**9))))
    return rows[0].get("ref", "")

scripts = []
for r in cand.get("EVID_SCRIPT", []):
    if r.get("source") == "obligation_required_script" and r.get("ref"):
        scripts.append(r["ref"])
if not scripts:
    s = pick_best("EVID_SCRIPT")
    if s:
        scripts = [s]

gate = pick_best("EVID_GATE_REPORT")
theorem = pick_best("EVID_THEOREM")
diff = pick_best("EVID_DIFFERENTIAL_LOG")

for s in scripts:
    print(f"WITH\t{s}")
if gate:
    print(f"GATE\t{gate}")
if theorem and "EVID_THEOREM" in required:
    print(f"THEOREM\t{theorem}")
if diff and "EVID_DIFFERENTIAL_LOG" in required:
    print(f"DIFF\t{diff}")
PY
)"
      while IFS=$'\t' read -r kind ref; do
        [[ -z "${kind}" || -z "${ref}" ]] && continue
        case "${kind}" in
          WITH) resolved_with+=("${ref}") ;;
          GATE) resolved_gate="${ref}" ;;
          THEOREM) resolved_theorem+=("${ref}") ;;
          DIFF) resolved_diff+=("${ref}") ;;
        esac
      done <<<"${_resolved}"

      if [[ ${#resolved_with[@]} -eq 0 ]]; then
        echo "worker process-messages: could not auto-resolve required script evidence for ${assignment_ref}" >&2
        exit 1
      fi
      AUTO_REPORT=1
    fi

    cmd=(./control-plane/scripts/collab_fulfill.sh --message-ref "${msg_ref}" --worktree "${WORKTREE}")
    if [[ ${#WITH_ITEMS[@]} -gt 0 ]]; then
      for x in "${WITH_ITEMS[@]}"; do cmd+=(--with "$x"); done
    else
      for x in "${resolved_with[@]}"; do cmd+=(--with "$x"); done
    fi
    for x in "${SCRIPT_REFS[@]}"; do cmd+=(--script "$x"); done
    if [[ ${#GATE_REFS[@]} -gt 0 ]]; then
      for x in "${GATE_REFS[@]}"; do cmd+=(--gate-report "$x"); done
    elif [[ -n "${resolved_gate}" ]]; then
      cmd+=(--gate-report "${resolved_gate}")
    fi
    for x in "${THEOREM_REFS[@]}"; do cmd+=(--theorem "$x"); done
    for x in "${resolved_theorem[@]}"; do cmd+=(--theorem "$x"); done
    for x in "${DIFFLOG_REFS[@]}"; do cmd+=(--diff-log "$x"); done
    for x in "${resolved_diff[@]}"; do cmd+=(--diff-log "$x"); done
    for x in "${RAW_EVIDENCE[@]}"; do cmd+=(--evidence "$x"); done
    [[ "${LAZY}" -eq 1 ]] && cmd+=(--lazy)
    [[ "${AUTO_REPORT}" -eq 1 ]] && cmd+=(--auto-report)
    cmd+=(--summary)
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      cmd+=(--dry-run)
    elif [[ "${NO_COMMIT}" -eq 0 ]]; then
      cmd+=(--auto-commit)
    fi
    "${cmd[@]}"
    continue
  fi

  echo "worker process-messages: unsupported next_action=${next_action}" >&2
  exit 1
done

./control-plane/scripts/collab_status.sh --worktree "${WORKTREE}"
