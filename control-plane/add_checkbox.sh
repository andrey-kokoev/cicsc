#!/usr/bin/env bash
#==============================================================================
# add_checkbox.sh - Add checkboxes to existing phase/milestone
#
# Usage:
#   ./add_checkbox.sh --milestone BZ1 --checkbox "BZ1.1:description" [--checkbox "BZ1.2:desc"]
#   ./add_checkbox.sh --milestone BZ1 --create-milestone --checkbox "BZ1.1:description"
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"
source "$SCRIPT_DIR/output.sh"

ensure_sync_precondition() {
    local local_head remote_head
    local_head=$(git rev-parse HEAD)
    remote_head=$(git rev-parse origin/main 2>/dev/null) || return 0
    if [[ "$local_head" != "$remote_head" ]]; then
        echo "ERROR: Worktree is not at origin/main." >&2
        echo "Refusing implicit git fetch/rebase in state mutation script." >&2
        echo "Run sync explicitly, then retry." >&2
        exit 1
    fi
}

ensure_sync_precondition

MILESTONE=""
CREATE_MILESTONE=0
CHECKBOXES=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --help|-h)
            echo "Usage: $0 --milestone <id> [--create-milestone] --checkbox 'id:desc' [--checkbox 'id:desc' ...]"
            exit 0
            ;;
        --milestone) MILESTONE="$2"; shift 2 ;;
        --create-milestone) CREATE_MILESTONE=1; shift ;;
        --checkbox)
            CHECKBOXES+=("$2")
            shift 2
            ;;
        *) echo "Unknown: $1"; exit 1 ;;
    esac
done

if [[ -z "$MILESTONE" || ${#CHECKBOXES[@]} -eq 0 ]]; then
    echo "Usage: $0 --milestone <id> [--create-milestone] --checkbox 'id:desc' [--checkbox 'id:desc' ...]"
    exit 1
fi

python3 - "$MILESTONE" "$CREATE_MILESTONE" "${CHECKBOXES[@]}" << 'PY'
import re
import sys
sys.path.insert(0, "control-plane")
from db import get_milestone, get_phase, add_milestone, add_checkbox

milestone_id = sys.argv[1]
create_milestone = bool(int(sys.argv[2]))
checkboxes = sys.argv[3:]

ms = get_milestone(milestone_id)
if not ms:
    if not create_milestone:
        print(f"ERROR: Milestone {milestone_id} not found", file=sys.stderr)
        print("Pass --create-milestone to create it on demand.", file=sys.stderr)
        sys.exit(1)

    m = re.fullmatch(r"([A-Za-z]{1,3})(\d+)", milestone_id)
    if not m:
        print(
            f"ERROR: Cannot infer phase from milestone id {milestone_id}",
            file=sys.stderr,
        )
        print("Expected milestone format like CG1.", file=sys.stderr)
        sys.exit(1)

    phase_id = m.group(1).upper()
    if get_phase(phase_id) is None:
        print(
            f"ERROR: Cannot create milestone {milestone_id}; phase {phase_id} not found",
            file=sys.stderr,
        )
        sys.exit(1)

    add_milestone(milestone_id, phase_id, f"Milestone {milestone_id}")
    print(f"Created milestone {milestone_id} in phase {phase_id}")

for cb_str in checkboxes:
    cb_id, cb_desc = cb_str.split(":", 1)
    add_checkbox(cb_id, milestone_id, "open", cb_desc)

print(f"Added {len(checkboxes)} checkboxes to {milestone_id}")
PY

emit_result ok add_checkbox "checkboxes added" "milestone=$MILESTONE" "count=${#CHECKBOXES[@]}"
