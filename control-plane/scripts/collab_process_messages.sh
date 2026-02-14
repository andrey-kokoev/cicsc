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

Worker fulfill options (required for full worker lifecycle):
  --with <path|cmd>
  --script <path>
  --gate-report <path>
  --theorem <path>
  --diff-log <path>
  --evidence <ref|EVID_KIND>
  --lazy
  --auto-report
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
  main_args=()
  if [[ -n "${AGENT_REF}" ]]; then
    main_args+=(--agent-ref "${AGENT_REF}")
  fi
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status fulfilled --count 0 --dry-run
    ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status ingested --count 0 --dry-run
    exit 0
  fi

  if [[ "${NO_COMMIT}" -eq 1 ]]; then
    ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status fulfilled --count 0 --no-commit
    ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status ingested --count 0 --no-commit
    ./control-plane/scripts/generate_views.sh >/dev/null
    ./control-plane/scripts/collab_validate.sh >/dev/null
  else
    ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status fulfilled --count 0 --subject "governance/collab: process messages (main/fulfilled)"
    ./control-plane/scripts/collab_close_batch.sh "${main_args[@]}" --status ingested --count 0 --subject "governance/collab: process messages (main/ingested)"
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
    if [[ "${needs_evidence}" -eq 0 ]]; then
      echo "worker process-messages halted: acknowledged work requires fulfill evidence flags (--with/--script/--gate-report/etc)." >&2
      exit 1
    fi
    msg_ref="$(python3 - "$status_json" <<'PY'
import json,sys
d=json.loads(sys.argv[1])
arr=d.get('in_progress',[])
print(arr[0].get('message_id','') if arr else '')
PY
)"
    if [[ -z "${msg_ref}" ]]; then
      echo "worker process-messages: missing acknowledged message_ref" >&2
      exit 1
    fi
    cmd=(./control-plane/scripts/collab_fulfill.sh --message-ref "${msg_ref}" --worktree "${WORKTREE}")
    for x in "${WITH_ITEMS[@]}"; do cmd+=(--with "$x"); done
    for x in "${SCRIPT_REFS[@]}"; do cmd+=(--script "$x"); done
    for x in "${GATE_REFS[@]}"; do cmd+=(--gate-report "$x"); done
    for x in "${THEOREM_REFS[@]}"; do cmd+=(--theorem "$x"); done
    for x in "${DIFFLOG_REFS[@]}"; do cmd+=(--diff-log "$x"); done
    for x in "${RAW_EVIDENCE[@]}"; do cmd+=(--evidence "$x"); done
    [[ "${LAZY}" -eq 1 ]] && cmd+=(--lazy)
    [[ "${AUTO_REPORT}" -eq 1 ]] && cmd+=(--auto-report)
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
