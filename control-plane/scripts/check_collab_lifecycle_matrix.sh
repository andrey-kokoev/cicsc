#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
cd "${ROOT_DIR}"

WORKTREE_KIMI="/home/andrey/src/cicsc/worktrees/kimi"

# 1) claim-next no actionable should exit 0 with explicit message.
claim_out="$(./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE_KIMI}" --dry-run 2>&1 || true)"
if ! grep -Fq "no actionable inbox messages" <<<"${claim_out}"; then
  echo "matrix fail: expected no-actionable message in claim-next dry-run"
  exit 1
fi

# 2) status JSON must be present and machine-readable.
status_json="$(./control-plane/scripts/collab_status.sh --worktree "${WORKTREE_KIMI}" --json)"
python3 - "${status_json}" <<'PY'
import json
import sys
doc = json.loads(sys.argv[1])
required = {"worktree", "in_progress", "actionable", "next_action", "next_detail", "next_command", "script_hints"}
missing = sorted(required - set(doc))
if missing:
    raise SystemExit(f"missing status keys: {missing}")
PY

# 3) show-assignment must fail for unknown assignment.
set +e
bad_show="$(./control-plane/scripts/collab_show_assignment.sh --ref ASSIGN_DOES_NOT_EXIST 2>&1)"
bad_show_code=$?
set -e
if [[ "${bad_show_code}" -eq 0 ]]; then
  echo "matrix fail: expected non-zero for unknown assignment"
  exit 1
fi
if ! grep -Fq "assignment not found" <<<"${bad_show}"; then
  echo "matrix fail: missing unknown-assignment diagnostic"
  exit 1
fi

# 4) auto-commit guard must reject dirty working tree.
tmp_guard="control-plane/.tmp_collab_dirty_guard"
touch "${tmp_guard}"
set +e
guard_out="$(./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE_KIMI}" --auto-commit 2>&1)"
guard_code=$?
set -e
rm -f "${tmp_guard}"
if [[ "${guard_code}" -eq 0 ]]; then
  echo "matrix fail: expected auto-commit dirty-tree guard failure"
  exit 1
fi
if ! grep -Fq "auto-commit requires a clean working tree" <<<"${guard_out}"; then
  echo "matrix fail: missing clean-tree guard diagnostic"
  exit 1
fi

# 5) run-loop must terminate cleanly in dry-run mode.
loop_out="$(./control-plane/scripts/collab_run_loop.sh --worktree "${WORKTREE_KIMI}" --max-steps 1 --dry-run 2>&1)"
if ! grep -Fq "run-loop: step=" <<<"${loop_out}"; then
  echo "matrix fail: missing run-loop step telemetry"
  exit 1
fi

# 6) revert guard: fulfilled -> sent must be blocked without --force.
set +e
revert_out="$(
  ./control-plane/scripts/collab_revert.sh \
    --message-ref MSG_PHASE34_AY24_KIMI_MULTI4_DISPATCH \
    --to-status sent \
    --reason "matrix guard check" \
    --dry-run 2>&1
)"
revert_code=$?
set -e
if [[ "${revert_code}" -eq 0 ]]; then
  echo "matrix fail: expected revert guard failure for fulfilled->sent without force"
  exit 1
fi
if ! grep -Fq "revert blocked: unsupported source->target without --force" <<<"${revert_out}"; then
  echo "matrix fail: missing revert guard diagnostic"
  exit 1
fi

echo "collab lifecycle matrix check passed"
