#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

SKIP_SYNC=0
NEW_ARGS=()
for arg in "$@"; do
    if [[ "$arg" == "--no-sync" ]]; then
        SKIP_SYNC=1
    else
        NEW_ARGS+=("$arg")
    fi
done
set -- "${NEW_ARGS[@]}"

needs_sync() {
    local local_head remote_head
    local_head=$(git rev-parse HEAD)
    remote_head=$(git rev-parse origin/main 2>/dev/null) || return 1
    [[ "$local_head" != "$remote_head" ]]
}

if [[ "$SKIP_SYNC" -eq 0 ]] && needs_sync 2>/dev/null; then
    echo "⚠ Worktree is behind origin/main. Fetching..."
    git fetch origin
    git stash || true
    git rebase origin/main || {
        echo "ERROR: Rebase failed. Resolve conflicts manually."
        git stash pop || true
        exit 1
    }
    git stash pop || true
    echo "  ✅ Synced"
fi

if [[ "${1:-}" == "--batch" ]]; then
    shift
    CHECKBOXES=("$@")
    if [[ ${#CHECKBOXES[@]} -eq 0 ]]; then
        echo "Usage: $0 --batch CHECKBOX1 CHECKBOX2 ..."
        exit 1
    fi
    BATCH_MODE=1
    COMMIT="$(git rev-parse --short HEAD)"
else
    CHECKBOXES=("$1")
    COMMIT="${2:-$(git rev-parse --short HEAD)}"
    BATCH_MODE=0
fi

echo "Running gates..."
if ! ./control-plane/check_gates.sh; then
    echo "Gates failed - cannot complete" >&2
    exit 1
fi

export BATCH_MODE
export CHECKBOXES_STR="${CHECKBOXES[*]}"
export COMMIT

python3 << 'PY'
import sys
import os
sys.path.insert(0, "control-plane")
from db import get_assignment, update_assignment, update_checkbox_status
from datetime import datetime

batch_mode = bool(int(os.environ["BATCH_MODE"]))
checkbox_list = os.environ["CHECKBOXES_STR"].split()
commit = os.environ["COMMIT"]

for checkbox in checkbox_list:
    assignment = get_assignment(checkbox)
    if not assignment or assignment["status"] != "in_progress":
        print(f"ERROR: No in_progress assignment for {checkbox}", file=sys.stderr)
        sys.exit(1)

    update_assignment(checkbox, status="done", commit_sha=commit, completed_at=datetime.now().isoformat() + "Z")
    update_checkbox_status(checkbox, "done")

if batch_mode:
    print(f"Completed batch: {', '.join(checkbox_list)} at commit {commit}")
else:
    print(f"Completed {checkbox_list[0]} at commit {commit}")
PY
