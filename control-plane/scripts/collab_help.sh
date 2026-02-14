#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
ROLE="worker"
WORKTREE="${PWD}"

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_help.sh [options]

Options:
  --role <worker|main>   Show worker-loop or main-dispatch flow (default: worker).
  --worktree <path>      Worktree path to render in command templates (default: $PWD).
  -h, --help             Show this message.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --role) ROLE="${2:-}"; shift 2 ;;
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ "${ROLE}" != "worker" && "${ROLE}" != "main" ]]; then
  echo "--role must be worker or main" >&2
  exit 1
fi

cat <<EOF
WMCC Quickstart (${ROLE})
Repository: ${ROOT_DIR}
Worktree: ${WORKTREE}

EOF

if [[ "${ROLE}" == "worker" ]]; then
  cat <<EOF
1) Refresh generated views:
   ./control-plane/scripts/generate_views.sh

2) Inspect actionable inbox for this worktree:
   ./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --refresh --actionable-only

3) Claim next actionable message and print obligation guidance:
   ./control-plane/scripts/collab_run_once.sh --worktree "${WORKTREE}"

4) Fulfill with typed evidence:
   ./control-plane/scripts/collab_fulfill.sh --message-ref MSG_... --worktree "${WORKTREE}" --script scripts/check_x.sh --gate-report docs/pilot/report.json

5) Watch for stale inbox:
   ./control-plane/scripts/collab_stale_watch.sh --warn-hours 24 --fail-hours 72
EOF
else
  cat <<EOF
1) Refresh generated views:
   ./control-plane/scripts/generate_views.sh

2) Dispatch assignment message:
   ./control-plane/scripts/collab_dispatch.sh --assignment-ref ASSIGN_... --payload-ref control-plane/collaboration/collab-model.yaml

3) Optionally delegate effective ownership for a worktree:
   ./control-plane/scripts/collab_delegate_worktree.sh --worktree /home/andrey/src/cicsc/worktrees/kimi --owner-agent-ref AGENT_MAIN --delegate-to AGENT_KIMI

4) Ingest and close after fulfillment:
   ./control-plane/scripts/collab_close_ingested.sh --message-ref MSG_... --commit \$(git rev-parse --short HEAD)
EOF
fi
