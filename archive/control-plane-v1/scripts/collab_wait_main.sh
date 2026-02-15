#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

INTERVAL_SECONDS=5
TIMEOUT_SECONDS=0
AGENT_REF=""
FRICTION_DECISION="accept_later"
FRICTION_BACKLOG_REF=""
FRICTION_NOTES=""
NO_REFRESH=0
QUIET=0
PROCESS_MODE=1

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_wait_main.sh [options]

Options:
  --interval-seconds <n>    Poll interval seconds (default: 5).
  --timeout-seconds <n>     Max wait seconds (0 = no timeout; default: 0).
  --agent-ref <id>          Optional main process filter (for collab_process_messages --agent-ref).
  --friction-decision <accept_now|accept_later|reject>
                            Friction triage decision when processing on wake (default: accept_later).
  --friction-backlog-ref <id>
                            Optional backlog ref for accept_later triage.
  --friction-notes <text>   Optional notes attached to friction triage.
  --no-refresh              Do not refresh mailbox views on each poll.
  --status-only             Wait and print actionable messages, but do not auto-process.
  --quiet                   Reduce output verbosity.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --interval-seconds) INTERVAL_SECONDS="${2:-}"; shift 2 ;;
    --timeout-seconds) TIMEOUT_SECONDS="${2:-}"; shift 2 ;;
    --agent-ref) AGENT_REF="${2:-}"; shift 2 ;;
    --friction-decision) FRICTION_DECISION="${2:-}"; shift 2 ;;
    --friction-backlog-ref) FRICTION_BACKLOG_REF="${2:-}"; shift 2 ;;
    --friction-notes) FRICTION_NOTES="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --status-only) PROCESS_MODE=0; shift ;;
    --quiet) QUIET=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "${INTERVAL_SECONDS}" =~ ^[0-9]+$ ]] || [[ "${INTERVAL_SECONDS}" -lt 1 ]]; then
  echo "--interval-seconds must be a positive integer" >&2
  exit 1
fi
if ! [[ "${TIMEOUT_SECONDS}" =~ ^[0-9]+$ ]]; then
  echo "--timeout-seconds must be an integer >= 0" >&2
  exit 1
fi

wait_cmd=(
  ./control-plane/scripts/collab_wait_for_messages.sh
  --worktree /home/andrey/src/cicsc
  --interval-seconds "${INTERVAL_SECONDS}"
  --timeout-seconds "${TIMEOUT_SECONDS}"
)
[[ "${NO_REFRESH}" -eq 1 ]] && wait_cmd+=(--no-refresh)
[[ "${QUIET}" -eq 1 ]] && wait_cmd+=(--quiet --no-json)

cd "${ROOT_DIR}"
"${wait_cmd[@]}"

if [[ "${PROCESS_MODE}" -eq 0 ]]; then
  exit 0
fi

proc_cmd=(
  ./control-plane/scripts/collab_process_messages.sh
  --role main
  --with-friction-triage
  --friction-decision "${FRICTION_DECISION}"
)
[[ -n "${AGENT_REF}" ]] && proc_cmd+=(--agent-ref "${AGENT_REF}")
[[ -n "${FRICTION_BACKLOG_REF}" ]] && proc_cmd+=(--friction-backlog-ref "${FRICTION_BACKLOG_REF}")
[[ -n "${FRICTION_NOTES}" ]] && proc_cmd+=(--friction-notes "${FRICTION_NOTES}")

"${proc_cmd[@]}"
