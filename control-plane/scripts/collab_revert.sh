#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

MESSAGE_REF=""
TO_STATUS="sent"
REASON=""
ACTOR_AGENT_REF="AGENT_MAIN"
COMMIT_SHA=""
NO_REFRESH=0
DRY_RUN=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_revert.sh --message-ref MSG_... --reason <text> [options]

Options:
  --to-status <s>        Target status after revert (sent|queued|rescinded; default: sent).
  --actor-agent-ref <id> Event actor (default: AGENT_MAIN).
  --commit <sha>         Commit to bind on event (default: current HEAD short).
  --no-refresh           Do not regenerate views after update.
  --dry-run              Validate and print action without mutation.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --to-status) TO_STATUS="${2:-}"; shift 2 ;;
    --reason) REASON="${2:-}"; shift 2 ;;
    --actor-agent-ref) ACTOR_AGENT_REF="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${MESSAGE_REF}" || -z "${REASON}" ]]; then
  echo "--message-ref and --reason are required" >&2
  usage >&2
  exit 1
fi
case "${TO_STATUS}" in
  sent|queued|rescinded) ;;
  *) echo "unsupported --to-status '${TO_STATUS}'" >&2; exit 1 ;;
esac

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

notes="Reverted via collab_revert.sh: ${REASON}"

cmd=(
  ./control-plane/scripts/collab_append_event.sh
  --message-ref "${MESSAGE_REF}"
  --to-status "${TO_STATUS}"
  --actor-agent-ref "${ACTOR_AGENT_REF}"
  --commit "${COMMIT_SHA}"
  --notes "${notes}"
)
if [[ "${TO_STATUS}" == "rescinded" ]]; then
  cmd+=(--rescinded-reason "${REASON}")
fi
if [[ "${NO_REFRESH}" -eq 1 ]]; then
  cmd+=(--no-refresh)
fi
if [[ "${DRY_RUN}" -eq 1 ]]; then
  cmd+=(--dry-run)
fi

"${cmd[@]}"

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would revert ${MESSAGE_REF} to ${TO_STATUS}"
else
  ./control-plane/scripts/collab_validate.sh >/dev/null
  echo "reverted message: ${MESSAGE_REF} -> ${TO_STATUS}"
fi
