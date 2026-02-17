#!/usr/bin/env bash
#==============================================================================
# add_phase.sh - Add new phase to execution ledger
#
# Usage:
#   ./add_phase.sh --id BZ --number 52 --title "Phase Title" --description "desc"
#   ./add_phase.sh --id BZ --number 52 --title "Phase Title" --checkboxes "BZ1.1:desc,BZ1.2:desc"
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

ID=""
NUMBER=""
TITLE=""
DESCRIPTION=""
CHECKBOXES=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --help|-h)
            echo "Usage: $0 --id <phase_id> --number <num> --title <title> [--description <desc>] [--checkboxes 'id:desc,id:desc']"
            exit 0
            ;;
        --id) ID="$2"; shift 2 ;;
        --number) NUMBER="$2"; shift 2 ;;
        --title) TITLE="$2"; shift 2 ;;
        --description) DESCRIPTION="$2"; shift 2 ;;
        --checkboxes) CHECKBOXES="$2"; shift 2 ;;
        *) echo "Unknown: $1"; exit 1 ;;
    esac
done

if [[ -z "$ID" || -z "$NUMBER" || -z "$TITLE" ]]; then
    echo "Usage: $0 --id <phase_id> --number <num> --title <title> [--description <desc>] [--checkboxes 'id:desc,id:desc']"
    exit 1
fi

python3 - "$ID" "$NUMBER" "$TITLE" "$DESCRIPTION" "$CHECKBOXES" << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import add_phase, add_milestone, add_checkbox

phase_id = sys.argv[1]
number = int(sys.argv[2])
title = sys.argv[3]
description = sys.argv[4]
checkboxes_str = sys.argv[5] if len(sys.argv) > 5 else ""

add_phase(phase_id, number, "in_progress", title, description)

milestone_checkboxes = []
if checkboxes_str:
    for cb in checkboxes_str.split(","):
        if ":" in cb:
            cb_id, cb_desc = cb.split(":", 1)
            milestone_checkboxes.append({"id": cb_id, "description": cb_desc})

if milestone_checkboxes:
    first_id = milestone_checkboxes[0]["id"]
    milestone_id = ".".join(first_id.split(".")[:-1])
    add_milestone(milestone_id, phase_id, f"Milestone {milestone_id}")
    for cb in milestone_checkboxes:
        add_checkbox(cb["id"], milestone_id, "open", cb["description"])

print(f"Added phase {phase_id} with {len(milestone_checkboxes)} checkboxes")
PY
