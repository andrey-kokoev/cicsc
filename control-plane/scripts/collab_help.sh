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
   ./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --refresh
   # full history:
   ./control-plane/scripts/collab_inbox.sh --worktree "${WORKTREE}" --refresh --all

2.5) Fast sync repair (if gates complain views/model are stale):
   ./control-plane/scripts/collab_sync.sh

3) Claim next actionable message and print obligation guidance:
   ./control-plane/scripts/collab_run_once.sh --worktree "${WORKTREE}"
   # one-command claim+commit:
   ./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE}" --commit

4) Fulfill with typed evidence:
   ./control-plane/scripts/collab_fulfill.sh --message-ref MSG_... --worktree "${WORKTREE}" --with scripts/check_x.sh --auto-report --lazy --auto-commit --message "phaseXX ayY.Y fulfill ..."

5) Batch/sweep homogeneous assignments:
   ./control-plane/scripts/collab_sweep.sh --worktree "${WORKTREE}" --with scripts/check_x.sh --auto-report --lazy
   # optional branch summary:
   ./control-plane/scripts/collab_sweep.sh --worktree "${WORKTREE}" --with scripts/check_x.sh --auto-report --lazy --checkout-branch

6) Revert mistaken claim:
   ./control-plane/scripts/collab_revert.sh --message-ref MSG_... --reason "claimed wrong assignment"

7) Assignment diff + summary:
   ./control-plane/scripts/collab_diff.sh --assignment-ref ASSIGN_...
   ./control-plane/scripts/collab_summary.sh --worktree "${WORKTREE}" --since 2026-02-13

8) Interactive session:
   ./control-plane/scripts/collab_interactive.sh --worktree "${WORKTREE}"

8.5) Fuzzy interactive picker (requires fzf):
   ./control-plane/scripts/collab_fzf.sh --worktree "${WORKTREE}"

9) Watch for stale inbox:
   ./control-plane/scripts/collab_stale_watch.sh --warn-hours 24 --fail-hours 72

10) Wait regime (poll every 5s; wake when actionable arrives):
   ./control-plane/scripts/collab_wait_for_messages.sh --worktree "${WORKTREE}" --interval-seconds 5
   # auto-run worker loop on wake:
   ./control-plane/scripts/collab_wait_for_messages.sh --worktree "${WORKTREE}" --interval-seconds 5 --run-on-found "./control-plane/scripts/collab_process_messages.sh --role worker --worktree ${WORKTREE}"

11) One-command protocol loop:
   ./control-plane/scripts/collab_process_messages.sh --role worker --worktree "${WORKTREE}"
   # optional explicit overrides:
   ./control-plane/scripts/collab_process_messages.sh --role worker --worktree "${WORKTREE}" --with scripts/check_x.sh --auto-report --lazy

11) Request friction reduction (typed request to triage authority):
   ./control-plane/scripts/collab_request_friction.sh --worktree "${WORKTREE}" --type ergonomics --severity medium --summary "claim loop is too verbose" --repro-step "run collab_claim_next.sh then collab_fulfill.sh repeatedly"
EOF
else
  cat <<EOF
1) Refresh generated views:
   ./control-plane/scripts/generate_views.sh

2) Dispatch assignment message:
   ./control-plane/scripts/collab_dispatch.sh --assignment-ref ASSIGN_... --payload-ref control-plane/collaboration/collab-model.yaml

2.5) Batch dispatch next N open checkboxes to an agent (single command):
   ./control-plane/scripts/collab_dispatch_batch.sh --agent-ref AGENT_KIMI --count 2
   # planned run (no mutation):
   ./control-plane/scripts/collab_dispatch_batch.sh --agent-ref AGENT_KIMI --phase 35 --count 2 --plan-only --run-id phase35-kimi
   # apply existing run:
   ./control-plane/scripts/collab_dispatch_batch.sh --agent-ref AGENT_KIMI --apply-run control-plane/logs/dispatch-runs/phase35-kimi.json
   # resume failed/pending rows:
   ./control-plane/scripts/collab_dispatch_batch.sh --agent-ref AGENT_KIMI --resume phase35-kimi

3) Optionally delegate effective ownership for a worktree:
   ./control-plane/scripts/collab_delegate_worktree.sh --worktree /home/andrey/src/cicsc/worktrees/kimi --owner-agent-ref AGENT_MAIN --delegate-to AGENT_KIMI

4) Ingest and close after fulfillment:
   ./control-plane/scripts/collab_close_ingested.sh --message-ref MSG_... --commit \$(git rev-parse --short HEAD)
   # close many at once:
   ./control-plane/scripts/collab_close_batch.sh --agent-ref AGENT_KIMI --status fulfilled --count 10

5) Main dashboard:
   ./control-plane/scripts/collab_main_status.sh --refresh

6) One-command main processing loop:
   ./control-plane/scripts/collab_process_messages.sh --role main --agent-ref AGENT_KIMI
   # full-cycle mode (close fulfilled/ingested + triage friction requests):
   ./control-plane/scripts/collab_process_messages.sh --role main --agent-ref AGENT_KIMI --with-friction-triage --friction-decision accept_later --friction-backlog-ref phase36.collab-ergonomics

7) Triage friction requests:
   ./control-plane/scripts/collab_triage_friction.sh --message-ref MSG_... --decision accept_now --notes "scheduled in next hardening batch"
EOF
fi
