#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
SCRIPT_REF=""
GATE_REPORT=""
WITH_ITEMS=()
AUTO_REPORT=0
INTERACTIVE=0
MAX_ITEMS=100
LAZY=0
MAX_AGE_MINUTES=30
COMMIT_EACH=1
CHECKOUT_BRANCH=0
BRANCHES_TOUCHED=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_sweep.sh --worktree <path> [--with <path-or-cmd> | --script <path> --gate-report <path>] [options]

Options:
  --with <path|cmd>     Sugar: execute script and bind EVID_SCRIPT. Repeatable.
  --auto-report         Auto-pick gate report when using --with/--script.
  --interactive         Ask y/n/skip before processing each assignment.
  --max-items <n>       Maximum assignments to process this run (default: 100).
  --lazy                Enable lazy run-script logic in fulfill.
  --max-age-minutes <n> Freshness TTL for --lazy (default: 30).
  --checkout-branch     Checkout assignment branch when claiming.
  --no-commit           Do not auto-commit per fulfilled assignment.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --script) SCRIPT_REF="${2:-}"; shift 2 ;;
    --gate-report) GATE_REPORT="${2:-}"; shift 2 ;;
    --with) WITH_ITEMS+=("${2:-}"); shift 2 ;;
    --auto-report|--report-auto) AUTO_REPORT=1; shift ;;
    --interactive) INTERACTIVE=1; shift ;;
    --max-items) MAX_ITEMS="${2:-}"; shift 2 ;;
    --lazy) LAZY=1; shift ;;
    --max-age-minutes) MAX_AGE_MINUTES="${2:-}"; shift 2 ;;
    --checkout-branch) CHECKOUT_BRANCH=1; shift ;;
    --no-commit) COMMIT_EACH=0; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ ${#WITH_ITEMS[@]} -eq 0 && -z "${SCRIPT_REF}" ]]; then
  echo "either --with or --script is required" >&2
  usage >&2
  exit 1
fi
if [[ ${#WITH_ITEMS[@]} -eq 0 && "${AUTO_REPORT}" -eq 0 && -z "${GATE_REPORT}" ]]; then
  echo "--gate-report is required unless --auto-report or --with is used" >&2
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
    claim_cmd=(./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE}")
    if [[ "${CHECKOUT_BRANCH}" -eq 1 ]]; then
      claim_cmd+=(--checkout-branch)
      # Collect touched branch for end-of-run summary.
      b="$(python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$WORKTREE" <<'PY'
import sys
from pathlib import Path
import yaml
c = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
wt = sys.argv[2]
msgs = [m for m in c.get("messages", []) if m.get("to_worktree")==wt]
evs = {}
for e in c.get("message_events", []):
  evs.setdefault(e.get("message_ref"), []).append(e)
actionable = []
for m in msgs:
  cur = sorted(evs.get(m.get("id"), []), key=lambda x:int(x.get("at_seq",0)))
  if not cur:
    continue
  s = cur[-1].get("to_status")
  if s in {"queued","sent"}:
    actionable.append(m)
if actionable:
  actionable = sorted(actionable, key=lambda m:m.get("id",""))
  print(actionable[0].get("branch",""))
PY
)"
      [[ -n "${b}" ]] && BRANCHES_TOUCHED+=("${b}")
    fi
    "${claim_cmd[@]}"
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
    --summary
    --max-age-minutes "${MAX_AGE_MINUTES}"
  )
  if [[ ${#WITH_ITEMS[@]} -gt 0 ]]; then
    for w in "${WITH_ITEMS[@]}"; do
      fulfill_cmd+=(--with "${w}")
    done
  else
    fulfill_cmd+=(--script "${SCRIPT_REF}" --run-script "${SCRIPT_REF}")
    if [[ -n "${GATE_REPORT}" ]]; then
      fulfill_cmd+=(--gate-report "${GATE_REPORT}")
    fi
  fi
  if [[ "${AUTO_REPORT}" -eq 1 ]]; then
    fulfill_cmd+=(--auto-report)
  fi
  if [[ "${LAZY}" -eq 1 ]]; then
    fulfill_cmd+=(--lazy)
    [[ -n "${SCRIPT_REF}" ]] && fulfill_cmd+=(--dep "${SCRIPT_REF}")
    [[ -n "${GATE_REPORT}" ]] && fulfill_cmd+=(--dep "${GATE_REPORT}")
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
if [[ "${CHECKOUT_BRANCH}" -eq 1 ]]; then
  if [[ ${#BRANCHES_TOUCHED[@]} -gt 0 ]]; then
    uniq_branches="$(printf '%s\n' "${BRANCHES_TOUCHED[@]}" | awk 'NF && !seen[$0]++' | paste -sd ', ' -)"
    echo "branches touched: ${uniq_branches}"
    echo "current: $(git -C "${WORKTREE}" branch --show-current 2>/dev/null || true)"
  else
    echo "branches touched: (none)"
  fi
fi
