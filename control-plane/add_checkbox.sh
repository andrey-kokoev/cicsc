#!/usr/bin/env bash
#==============================================================================
# add_checkbox.sh - Add checkboxes to existing phase/milestone
#
# Usage:
#   ./add_checkbox.sh --milestone BZ1 --checkbox "BZ1.1:description" [--checkbox "BZ1.2:desc"]
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

# Auto-sync if on worktree and behind main
needs_sync() {
    local local_head remote_head
    local_head=$(git rev-parse HEAD)
    remote_head=$(git rev-parse origin/main 2>/dev/null) || return 1
    [[ "$local_head" != "$remote_head" ]]
}

if needs_sync 2>/dev/null; then
    echo "⚠ Worktree is behind origin/main. Fetching..."
    git fetch origin
    git rebase origin/main
    echo "  ✅ Synced"
fi

MILESTONE=""
CHECKBOXES=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --help|-h)
            echo "Usage: $0 --milestone <id> --checkbox 'id:desc' [--checkbox 'id:desc' ...]"
            exit 0
            ;;
        --milestone) MILESTONE="$2"; shift 2 ;;
        --checkbox)
            CHECKBOXES+=("$2")
            shift 2
            ;;
        *) echo "Unknown: $1"; exit 1 ;;
    esac
done

if [[ -z "$MILESTONE" || ${#CHECKBOXES[@]} -eq 0 ]]; then
    echo "Usage: $0 --milestone <id> --checkbox 'id:desc' [--checkbox 'id:desc' ...]"
    exit 1
fi

python3 - "$MILESTONE" "${CHECKBOXES[@]}" << 'PY'
import yaml
import sys

milestone_id = sys.argv[1]
checkboxes = sys.argv[2:]

ledger = yaml.safe_load(open("control-plane/execution-ledger.yaml"))

# Find milestone
found = False
for ph in ledger.get("phases", []):
    for ms in ph.get("milestones", []):
        if ms.get("id") == milestone_id:
            for cb_str in checkboxes:
                cb_id, cb_desc = cb_str.split(":", 1)
                ms["checkboxes"].append({
                    "id": cb_id,
                    "status": "open",
                    "description": cb_desc
                })
            found = True
            break
    if found:
        break

if not found:
    print(f"ERROR: Milestone {milestone_id} not found", file=sys.stderr)
    sys.exit(1)

with open("control-plane/execution-ledger.yaml", "w") as f:
    yaml.dump(ledger, f, sort_keys=False, default_flow_style=False)

import os
os.chmod("control-plane/execution-ledger.yaml", 0o444)

print(f"Added {len(checkboxes)} checkboxes to {milestone_id}")
PY
