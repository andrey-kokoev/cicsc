#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_dry_run.sh <action> [args...]

Actions:
  claim-next   -> collab_claim_next.sh --dry-run
  fulfill      -> collab_fulfill.sh --dry-run
  close        -> collab_close_ingested.sh --dry-run
  dispatch     -> collab_dispatch.sh --dry-run
  delegate     -> collab_delegate_worktree.sh --dry-run
  append-event -> collab_append_event.sh --dry-run

Examples:
  ./control-plane/scripts/collab_dry_run.sh claim-next --worktree "$PWD"
  ./control-plane/scripts/collab_dry_run.sh fulfill --message-ref MSG_... --worktree "$PWD" --script scripts/check_x.sh --gate-report docs/pilot/report.json
USAGE
}

if [[ $# -lt 1 ]]; then
  usage >&2
  exit 1
fi

ACTION="$1"
shift || true

cd "${ROOT_DIR}"

case "${ACTION}" in
  claim-next)
    ./control-plane/scripts/collab_claim_next.sh --dry-run "$@"
    ;;
  fulfill)
    ./control-plane/scripts/collab_fulfill.sh --dry-run "$@"
    ;;
  close)
    ./control-plane/scripts/collab_close_ingested.sh --dry-run "$@"
    ;;
  dispatch)
    ./control-plane/scripts/collab_dispatch.sh --dry-run "$@"
    ;;
  delegate)
    ./control-plane/scripts/collab_delegate_worktree.sh --dry-run "$@"
    ;;
  append-event)
    ./control-plane/scripts/collab_append_event.sh --dry-run "$@"
    ;;
  -h|--help)
    usage
    ;;
  *)
    echo "unknown action: ${ACTION}" >&2
    usage >&2
    exit 1
    ;;
esac
