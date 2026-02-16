#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGENT="${1:-}"
SYNC_ARG=""
if [[ "${2:-}" == "--no-sync" ]]; then
    SYNC_ARG="--no-sync"
fi

# Check if we're on a worktree and need to sync
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

# Auto-sync if on worktree and behind main
if is_worktree && needs_sync 2>/dev/null; then
    echo "⚠ Worktree is behind origin/main. Fetching..."
    git fetch origin
    if [[ "$SYNC_ARG" == "--no-sync" ]]; then
        echo "  (sync skipped)"
    else
        echo "  Rebasing to origin/main..."
        git rebase origin/main
        echo "  ✅ Synced"
    fi
fi

python3 - "$AGENT" << 'PY'
import yaml
import sys
from pathlib import Path

agent = sys.argv[1] if len(sys.argv) > 1 else ""

assignments = yaml.safe_load(Path("control-plane/assignments.yaml").read_text())
ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())

# Build description lookup
descriptions = {}
for ph in ledger.get("phases", []):
    for ms in ph.get("milestones", []):
        for cb in ms.get("checkboxes", []):
            descriptions[cb["id"]] = cb.get("description", "No description")

open_count = 0
in_progress_count = 0

for a in assignments.get("assignments", []):
    if agent and a["agent_ref"] != agent:
        continue
    status = a["status"]
    cb = a["checkbox_ref"]
    ag = a["agent_ref"]
    desc = descriptions.get(cb, "")[:50]
    
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
