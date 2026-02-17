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
import sys
sys.path.insert(0, "control-plane")
from db import get_milestone, add_checkbox

milestone_id = sys.argv[1]
checkboxes = sys.argv[2:]

ms = get_milestone(milestone_id)
if not ms:
    print(f"ERROR: Milestone {milestone_id} not found", file=sys.stderr)
    sys.exit(1)

for cb_str in checkboxes:
    cb_id, cb_desc = cb_str.split(":", 1)
    add_checkbox(cb_id, milestone_id, "open", cb_desc)

print(f"Added {len(checkboxes)} checkboxes to {milestone_id}")
PY
