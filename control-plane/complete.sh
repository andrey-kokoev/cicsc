#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Check for --no-sync flag
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

# Auto-sync if on worktree and behind main
needs_sync() {
    local local_head remote_head
    local_head=$(git rev-parse HEAD)
    remote_head=$(git rev-parse origin/main 2>/dev/null) || return 1
    [[ "$local_head" != "$remote_head" ]]
}

if [[ "$SKIP_SYNC" -eq 0 ]] && needs_sync 2>/dev/null; then
    echo "⚠ Worktree is behind origin/main. Fetching..."
    git fetch origin
    git rebase origin/main || {
        echo "ERROR: Rebase failed. Resolve conflicts manually."
        exit 1
    }
    echo "  ✅ Synced"
fi

# Check for --batch flag
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

# Run gates once (before any updates)
echo "Running gates..."
if ! ./control-plane/check_gates.sh; then
    echo "Gates failed - cannot complete" >&2
    exit 1
fi

export BATCH_MODE
export CHECKBOXES_STR="${CHECKBOXES[*]}"
export COMMIT

python3 << 'PY'
import yaml
import sys
import os
from pathlib import Path
from datetime import datetime

batch_mode = bool(int(os.environ["BATCH_MODE"]))
checkbox_list = os.environ["CHECKBOXES_STR"].split()
commit = os.environ["COMMIT"]

ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())
assignments = yaml.safe_load(Path("control-plane/assignments.yaml").read_text())

for checkbox in checkbox_list:
    # Find and update assignment
    found = False
    for a in assignments.get("assignments", []):
        if a["checkbox_ref"] == checkbox and a["status"] == "in_progress":
            a["status"] = "done"
            a["commit"] = commit
            a["completed_at"] = datetime.now().isoformat() + "Z"
            found = True
            break

    if not found:
        print(f"ERROR: No in_progress assignment for {checkbox}", file=sys.stderr)
        sys.exit(1)

    # Update ledger
    for ph in ledger.get("phases", []):
        for ms in ph.get("milestones", []):
            for cb in ms.get("checkboxes", []):
                if cb["id"] == checkbox:
                    cb["status"] = "done"

Path("control-plane/assignments.yaml").write_text(yaml.dump(assignments, sort_keys=False))
Path("control-plane/execution-ledger.yaml").write_text(yaml.dump(ledger, sort_keys=False))

if batch_mode:
    print(f"Completed batch: {', '.join(checkbox_list)} at commit {commit}")
else:
    print(f"Completed {checkbox_list[0]} at commit {commit}")
PY
