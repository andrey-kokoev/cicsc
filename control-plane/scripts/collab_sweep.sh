#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
SCRIPT_REF=""
GATE_REPORT=""
INTERACTIVE=0
MAX_ITEMS=100
LAZY=0
MAX_AGE_MINUTES=30
COMMIT_EACH=1

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_sweep.sh --worktree <path> --script <path-or-cmd> --gate-report <path> [options]

Options:
  --interactive         Ask y/n/skip before processing each assignment.
  --max-items <n>       Maximum assignments to process this run (default: 100).
  --lazy                Enable lazy run-script logic in fulfill.
  --max-age-minutes <n> Freshness TTL for --lazy (default: 30).
  --no-commit           Do not auto-commit per fulfilled assignment.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --script) SCRIPT_REF="${2:-}"; shift 2 ;;
    --gate-report) GATE_REPORT="${2:-}"; shift 2 ;;
    --interactive) INTERACTIVE=1; shift ;;
    --max-items) MAX_ITEMS="${2:-}"; shift 2 ;;
    --lazy) LAZY=1; shift ;;
    --max-age-minutes) MAX_AGE_MINUTES="${2:-}"; shift 2 ;;
    --no-commit) COMMIT_EACH=0; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${SCRIPT_REF}" || -z "${GATE_REPORT}" ]]; then
  echo "--script and --gate-report are required" >&2
  usage >&2
  exit 1
fi
if ! [[ "${MAX_ITEMS}" =~ ^[0-9]+$ ]] || [[ "${MAX_ITEMS}" -lt 1 ]]; then
  echo "--max-items must be a positive integer" >&2
  exit 1
fi
if ! [[ "${MAX_AGE_MINUTES}" =~ ^[0-9]+$ ]] || [[ "${MAX_AGE_MINUTES}" -lt 1 ]]; then
  echo "--max-age-minutes must be a positive integer" >&2
  exit 1
fi

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

processed=0
echo "sweep start: worktree=${WORKTREE} interactive=${INTERACTIVE} max_items=${MAX_ITEMS}"
while [[ "${processed}" -lt "${MAX_ITEMS}" ]]; do
  status_json="$(./control-plane/scripts/collab_status.sh --worktree "${WORKTREE}" --json)"
  _next="$(
    python3 - "${status_json}" <<'PY'
import json,sys
d=json.loads(sys.argv[1])
print(d.get("next_action","idle"))
in_progress=d.get("in_progress",[])
actionable=d.get("actionable",[])
if in_progress:
    print(in_progress[0].get("message_id",""))
    print(in_progress[0].get("assignment_ref",""))
elif actionable:
    print(actionable[0].get("message_id",""))
    print(actionable[0].get("assignment_ref",""))
else:
    print("")
    print("")
PY
)"
  readarray -t _lines <<<"${_next}"
  action="${_lines[0]:-idle}"
  msg="${_lines[1]:-}"
  assignment="${_lines[2]:-}"

  if [[ "${action}" == "idle" ]]; then
    echo "sweep: idle, no remaining work"
    break
  fi

  if [[ "${action}" == "claim_next_actionable" ]]; then
    ./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE}"
    status_json="$(./control-plane/scripts/collab_status.sh --worktree "${WORKTREE}" --json)"
    _ack="$(
      python3 - "${status_json}" <<'PY'
import json,sys
d=json.loads(sys.argv[1])
ip=d.get("in_progress",[])
if ip:
    print(ip[0].get("message_id",""))
    print(ip[0].get("assignment_ref",""))
PY
)"
    readarray -t _ack_lines <<<"${_ack}"
    msg="${_ack_lines[0]:-}"
    assignment="${_ack_lines[1]:-}"
  fi

  if [[ -z "${msg}" ]]; then
    echo "sweep: unable to resolve message at fulfill boundary" >&2
    exit 1
  fi

  if [[ "${INTERACTIVE}" -eq 1 ]]; then
    echo "assignment=${assignment} message=${msg}"
    read -r -p "process? [y/n/skip] " ans
    case "${ans}" in
      y|Y|yes|YES) ;;
      n|N|no|NO)
        echo "sweep: abort by operator"
        break
        ;;
      *)
        echo "sweep: skipping ${msg}"
        ./control-plane/scripts/collab_revert.sh --message-ref "${msg}" --to-status sent --reason "sweep skip"
        continue
        ;;
    esac
  fi

  fulfill_cmd=(
    ./control-plane/scripts/collab_fulfill.sh
    --message-ref "${msg}"
    --worktree "${WORKTREE}"
    --script "${SCRIPT_REF}"
    --gate-report "${GATE_REPORT}"
    --run-script "${SCRIPT_REF}"
    --max-age-minutes "${MAX_AGE_MINUTES}"
  )
  if [[ "${LAZY}" -eq 1 ]]; then
    fulfill_cmd+=(--lazy --dep "${SCRIPT_REF}" --dep "${GATE_REPORT}")
  fi
  if [[ "${COMMIT_EACH}" -eq 1 ]]; then
    fulfill_cmd+=(--auto-commit)
  fi
  "${fulfill_cmd[@]}"

  processed=$((processed + 1))
  echo "sweep: processed=${processed} assignment=${assignment}"
done

if [[ "${processed}" -ge "${MAX_ITEMS}" ]]; then
  echo "sweep: reached max_items=${MAX_ITEMS}"
fi
