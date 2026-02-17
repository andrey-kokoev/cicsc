#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGENT="$1"
FORCE_SYNC=1
SKIP_SYNC=0

# Parse optional flags
while [[ $# -gt 1 ]]; do
    case "$2" in
        --sync) FORCE_SYNC=1; SKIP_SYNC=0; shift ;;
        --no-sync) SKIP_SYNC=1; shift ;;
        *) break ;;
    esac
    shift
done

# Auto-sync if on worktree and behind main (unless --no-sync)
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
import yaml
import sys
from pathlib import Path
from datetime import datetime

agent = sys.argv[1]

assignments = yaml.safe_load(Path("control-plane/assignments.yaml").read_text())

claimed = []
for a in assignments.get("assignments", []):
    if a["agent_ref"] == agent and a["status"] == "open":
        a["status"] = "in_progress"
        a["started_at"] = datetime.now().isoformat() + "Z"
        claimed.append(a["checkbox_ref"])

if claimed:
    Path("control-plane/assignments.yaml").write_text(yaml.dump(assignments, sort_keys=False))
    for cb in claimed:
        print(f"Claimed {cb}")
else:
    print("No open assignments")
PY
