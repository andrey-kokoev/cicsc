#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGENT="$1"
FORCE_SYNC=1
SKIP_SYNC=0

while [[ $# -gt 1 ]]; do
    case "$2" in
        --sync) FORCE_SYNC=1; SKIP_SYNC=0; shift ;;
        --no-sync) SKIP_SYNC=1; shift ;;
        *) break ;;
    esac
    shift
done

needs_sync() {
    local local_head remote_head
    local_head=$(git rev-parse HEAD)
    remote_head=$(git rev-parse origin/main 2>/dev/null) || return 1
    [[ "$local_head" != "$remote_head" ]]
}

if [[ "$FORCE_SYNC" -eq 1 ]] && [[ "$SKIP_SYNC" -eq 0 ]] && needs_sync 2>/dev/null; then
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

python3 - "$AGENT" << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_assignments_by_agent, update_assignment
from datetime import datetime

agent = sys.argv[1]

assignments = get_assignments_by_agent(agent)
claimed = []

for a in assignments:
    if a["status"] == "open":
        update_assignment(a["checkbox_ref"], status="in_progress", started_at=datetime.now().isoformat() + "Z")
        claimed.append(a["checkbox_ref"])

if claimed:
    for cb in claimed:
        print(f"Claimed {cb}")
else:
    print("No open assignments")
PY
