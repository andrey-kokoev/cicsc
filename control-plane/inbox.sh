#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGENT="${1:-}"
SYNC_ARG=""
if [[ "${2:-}" == "--no-sync" ]]; then
    SYNC_ARG="--no-sync"
fi

is_worktree() {
    [[ $(git rev-parse --is-inside-work-tree 2>/dev/null) == "true" ]] && \
    [[ $(git rev-parse --is-inside-work-tree) != $(git rev-parse --is-inside-work-tree "$ROOT") ]]
}

needs_sync() {
    local local_head remote_head
    local_head=$(git rev-parse HEAD)
    remote_head=$(git rev-parse origin/main 2>/dev/null) || return 1
    [[ "$local_head" != "$remote_head" ]]
}

if is_worktree && needs_sync 2>/dev/null; then
    echo "⚠ Worktree is behind origin/main. Fetching..."
    git fetch origin
    if [[ "$SYNC_ARG" == "--no-sync" ]]; then
        echo "  (sync skipped)"
    else
        echo "  Rebasing to origin/main..."
        git stash || true
        git rebase origin/main || {
            echo "  Rebase failed, restoring..."
            git stash pop || true
        }
        git stash pop || true
        echo "  ✅ Synced"
    fi
fi

python3 - "$AGENT" << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_all_checkboxes, get_active_assignments

agent = sys.argv[1] if len(sys.argv) > 1 else ""

checkboxes = {cb["id"]: cb["description"] for cb in get_all_checkboxes()}
assignments = get_active_assignments()

open_count = 0
in_progress_count = 0

for a in assignments:
    if agent and a["agent_ref"] != agent:
        continue
    status = a["status"]
    cb = a["checkbox_ref"]
    ag = a["agent_ref"]
    desc = checkboxes.get(cb, "")[:50]
    
    if status == "open":
        open_count += 1
        if agent:
            print(f"[OPEN] {cb}")
            if desc:
                print(f"       {desc}...")
        else:
            print(f"[OPEN] {cb} -> {ag}")
    elif status == "in_progress":
        in_progress_count += 1
        if agent:
            print(f"[IN_PROGRESS] {cb}")
            if desc:
                print(f"              {desc}...")
        else:
            print(f"[IN_PROGRESS] {cb} -> {ag}")

if agent:
    print(f"\nTotal: {open_count} open, {in_progress_count} in_progress")
else:
    print(f"\nTotal active: {open_count + in_progress_count}")
PY
