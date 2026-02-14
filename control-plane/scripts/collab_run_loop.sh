#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
MAX_STEPS=20
DRY_RUN=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_run_loop.sh [--worktree <path>] [--max-steps <n>] [--dry-run]

Behavior:
  - claims next actionable message(s) for the target worktree
  - stops at the first fulfill boundary (acknowledged message)
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --max-steps) MAX_STEPS="${2:-}"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "${MAX_STEPS}" =~ ^[0-9]+$ ]] || [[ "${MAX_STEPS}" -lt 1 ]]; then
  echo "--max-steps must be a positive integer" >&2
  exit 1
fi

cd "${ROOT_DIR}"

echo "run-loop start: worktree=${WORKTREE} max_steps=${MAX_STEPS} dry_run=${DRY_RUN}"
steps=0
while [[ "${steps}" -lt "${MAX_STEPS}" ]]; do
  steps=$((steps + 1))
  status_json="$(./control-plane/scripts/collab_status.sh --worktree "${WORKTREE}" --json)"
  _resolved="$(
    python3 - "${status_json}" <<'PY'
import json
import sys

doc = json.loads(sys.argv[1])
action = doc.get("next_action")
detail = doc.get("next_detail", "")
cmd = doc.get("next_command", "")
in_progress = doc.get("in_progress", [])
first_ack = in_progress[0] if in_progress else {}
print(action or "")
print(detail)
print(cmd)
print(first_ack.get("message_id", ""))
print(first_ack.get("assignment_ref", ""))
PY
  )"
  readarray -t _lines <<<"${_resolved}"
  _action="${_lines[0]:-idle}"
  _detail="${_lines[1]:-}"
  _cmd="${_lines[2]:-}"
  _ack_msg="${_lines[3]:-}"
  _ack_assign="${_lines[4]:-}"
  echo "run-loop: step=${steps} action=${_action} detail=\"${_detail}\""

  if [[ "${_action}" == "idle" ]]; then
    echo "run-loop: step=${steps} result=idle_exit"
    break
  fi

  if [[ "${_action}" == "claim_next_actionable" ]]; then
    echo "run-loop: step=${steps} transition=claim_next_actionable"
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      ./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE}" --dry-run
      echo "run-loop: step=${steps} result=dry_run_claim_stop"
      break
    fi
    ./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE}"
    echo "run-loop: step=${steps} result=claimed_continue"
    continue
  fi

  if [[ "${_action}" == "fulfill_acknowledged_first" ]]; then
    echo "run-loop: step=${steps} result=fulfill_boundary"
    if [[ -n "${_ack_assign}" ]]; then
      echo "assignment: ${_ack_assign}"
      ./control-plane/scripts/collab_show_assignment.sh --ref "${_ack_assign}" | sed -n '1,24p'
    fi
    if [[ -n "${_ack_msg}" ]]; then
      echo "next:"
      echo "  ./control-plane/scripts/collab_fulfill.sh --message-ref ${_ack_msg} --worktree \"${WORKTREE}\" --script <path> --gate-report <path>"
    elif [[ -n "${_cmd}" ]]; then
      echo "next: ${_cmd}"
    fi
    break
  fi

  echo "run-loop: step=${steps} result=unknown_action_stop"
  break
done
if [[ "${steps}" -ge "${MAX_STEPS}" ]]; then
  echo "run-loop: result=max_steps_stop max_steps=${MAX_STEPS}"
fi
