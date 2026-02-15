#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_interactive.sh [--worktree <path>]
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"

echo "interactive session: worktree=${WORKTREE}"
while true; do
  ./control-plane/scripts/collab_status.sh --worktree "${WORKTREE}"
  status_json="$(./control-plane/scripts/collab_status.sh --worktree "${WORKTREE}" --json)"
  _next="$(
    python3 - "${status_json}" <<'PY'
import json,sys
d=json.loads(sys.argv[1])
print(d.get("next_action","idle"))
ip=d.get("in_progress",[])
if ip:
    print(ip[0].get("message_id",""))
    print(ip[0].get("assignment_ref",""))
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
    echo "No pending work."
    break
  fi

  if [[ "${action}" == "claim_next_actionable" ]]; then
    read -r -p "Claim next actionable message? [Y/n] " ans
    case "${ans}" in
      n|N|no|NO) echo "stopping"; break ;;
      *)
        ./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE}" --checkout-branch
        continue
        ;;
    esac
  fi

  if [[ "${action}" == "fulfill_acknowledged_first" ]]; then
    echo "Fulfill boundary: assignment=${assignment} message=${msg}"
    read -r -p "Script path or command to run: " script_ref
    read -r -p "Gate report path: " gate_report
    read -r -p "Use lazy mode? [y/N] " lazy_ans
    read -r -p "Auto-commit after fulfill? [Y/n] " auto_ans
    read -r -p "Custom commit subject (optional): " subj

    fulfill_cmd=(
      ./control-plane/scripts/collab_fulfill.sh
      --message-ref "${msg}"
      --worktree "${WORKTREE}"
      --script "${script_ref}"
      --gate-report "${gate_report}"
      --run-script "${script_ref}"
      --suggest-commit
    )
    case "${lazy_ans}" in
      y|Y|yes|YES) fulfill_cmd+=(--lazy --dep "${script_ref}" --dep "${gate_report}") ;;
    esac
    case "${auto_ans}" in
      n|N|no|NO) ;;
      *) fulfill_cmd+=(--auto-commit) ;;
    esac
    if [[ -n "${subj}" ]]; then
      fulfill_cmd+=(--commit-subject "${subj}")
    fi

    "${fulfill_cmd[@]}"
    continue
  fi

  echo "Unknown next action: ${action}"
  break
done
