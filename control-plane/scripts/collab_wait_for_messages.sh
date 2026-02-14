#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE=""
INTERVAL_SECONDS=5
TIMEOUT_SECONDS=0
REFRESH=1
RUN_ON_FOUND=""
QUIET=0
PRINT_JSON=1

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_wait_for_messages.sh [options]

Options:
  --worktree <path>         Target worktree mailbox key (required).
  --interval-seconds <n>    Poll interval in seconds (default: 5).
  --timeout-seconds <n>     Max wait time in seconds (0 = no timeout, default: 0).
  --no-refresh              Do not refresh generated views on each poll.
  --run-on-found <cmd>      Optional command to execute once actionable messages are found.
  --no-json                 Do not print full actionable inbox JSON on match.
  --quiet                   Reduce periodic status output.

Exit codes:
  0 => actionable messages found
  2 => timeout reached with no actionable messages
  1 => usage/validation error
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --interval-seconds) INTERVAL_SECONDS="${2:-}"; shift 2 ;;
    --timeout-seconds) TIMEOUT_SECONDS="${2:-}"; shift 2 ;;
    --no-refresh) REFRESH=0; shift ;;
    --run-on-found) RUN_ON_FOUND="${2:-}"; shift 2 ;;
    --quiet) QUIET=1; shift ;;
    --no-json) PRINT_JSON=0; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${WORKTREE}" ]]; then
  echo "--worktree is required" >&2
  usage >&2
  exit 1
fi
if ! [[ "${INTERVAL_SECONDS}" =~ ^[0-9]+$ ]] || [[ "${INTERVAL_SECONDS}" -lt 1 ]]; then
  echo "--interval-seconds must be a positive integer" >&2
  exit 1
fi
if ! [[ "${TIMEOUT_SECONDS}" =~ ^[0-9]+$ ]]; then
  echo "--timeout-seconds must be an integer >= 0" >&2
  exit 1
fi

cd "${ROOT_DIR}"

start_ts="$(date +%s)"
if [[ "${QUIET}" -eq 0 ]]; then
  echo "waiting for actionable messages: worktree=${WORKTREE} interval=${INTERVAL_SECONDS}s timeout=${TIMEOUT_SECONDS}s"
fi

while true; do
  inbox_cmd=(./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --actionable-only)
  if [[ "${REFRESH}" -eq 1 ]]; then
    inbox_cmd+=(--refresh)
  fi

  inbox_json="$(${inbox_cmd[@]})"
  count="$(python3 - "$inbox_json" <<'PY'
import json,sys
arr=json.loads(sys.argv[1])
print(len(arr))
PY
)"

  if [[ "${count}" -gt 0 ]]; then
    echo "actionable messages found: ${count}"
    python3 - "$inbox_json" <<'PY'
import json,sys
arr=json.loads(sys.argv[1])
for m in arr:
    print(f"- {m.get('id','')} {m.get('assignment_ref','')} [{m.get('current_status','')}]")
PY
    if [[ "${PRINT_JSON}" -eq 1 ]]; then
      echo "${inbox_json}"
    fi
    if [[ -n "${RUN_ON_FOUND}" ]]; then
      if [[ "${QUIET}" -eq 0 ]]; then
        echo "running on-found command: ${RUN_ON_FOUND}"
      fi
      bash -lc "${RUN_ON_FOUND}"
    fi
    exit 0
  fi

  now_ts="$(date +%s)"
  elapsed=$((now_ts - start_ts))
  if [[ "${TIMEOUT_SECONDS}" -gt 0 && "${elapsed}" -ge "${TIMEOUT_SECONDS}" ]]; then
    if [[ "${QUIET}" -eq 0 ]]; then
      echo "timeout reached after ${elapsed}s with no actionable messages"
    fi
    exit 2
  fi

  if [[ "${QUIET}" -eq 0 ]]; then
    echo "no actionable messages (elapsed=${elapsed}s); sleeping ${INTERVAL_SECONDS}s"
  fi
  sleep "${INTERVAL_SECONDS}"
done
