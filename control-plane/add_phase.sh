#!/usr/bin/env bash
#==============================================================================
# add_phase.sh - Add new phase to execution ledger
#
# Usage:
#   ./add_phase.sh --title "Phase Title" --description "desc"
#   ./add_phase.sh --number 52 --title "Phase Title"
#   ./add_phase.sh --id BZ --title "Phase Title" --checkboxes "BZ1.1:desc,BZ1.2:desc"
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

ID=""
NUMBER=""
TITLE=""
DESCRIPTION=""
CHECKBOXES=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --help|-h)
            echo "Usage: $0 [--id <phase_id>] [--number <num>] --title <title> [--description <desc>] [--checkboxes 'id:desc,id:desc']"
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

if [[ -z "$TITLE" ]]; then
    echo "Usage: $0 [--id <phase_id>] [--number <num>] --title <title> [--description <desc>] [--checkboxes 'id:desc,id:desc']"
    exit 1
fi

PY_OUT="$(python3 - "$ID" "$NUMBER" "$TITLE" "$DESCRIPTION" "$CHECKBOXES" << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import add_phase, add_milestone, add_checkbox, get_all_phases

phase_id = sys.argv[1]
number_arg = sys.argv[2]
title = sys.argv[3]
description = sys.argv[4]
checkboxes_str = sys.argv[5] if len(sys.argv) > 5 else ""

def phase_id_to_index(pid):
    if not pid or not pid.isalpha():
        return None
    s = pid.upper()
    if len(s) < 2:
        return None
    # AA..ZZ => 0..675, AAA.. => continues after two-letter space.
    offset = sum(26 ** k for k in range(2, len(s)))
    value = 0
    for ch in s:
        value = value * 26 + (ord(ch) - ord("A"))
    return offset + value

def index_to_phase_id(idx):
    if idx < 0:
        raise ValueError("phase id index must be non-negative")
    length = 2
    remaining = idx
    while remaining >= 26 ** length:
        remaining -= 26 ** length
        length += 1

    chars = ["A"] * length
    for pos in range(length - 1, -1, -1):
        remaining, rem = divmod(remaining, 26)
        chars[pos] = chr(ord("A") + rem)
    return "".join(chars)

if not phase_id:
    all_phases = get_all_phases()
    max_idx = -1
    for p in all_phases:
        idx = phase_id_to_index(str(p.get("id", "")))
        if idx is not None and idx > max_idx:
            max_idx = idx
    phase_id = index_to_phase_id(max_idx + 1 if max_idx >= 0 else 0)

all_phases = get_all_phases()
if number_arg:
    number = int(number_arg)
else:
    max_number = 0
    for p in all_phases:
        try:
            n = int(p.get("number", 0))
        except (TypeError, ValueError):
            n = 0
        if n > max_number:
            max_number = n
    number = max_number + 1

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
print(f"PHASE_ID={phase_id}")
PY
)"
echo "$PY_OUT"
PHASE_ID_LINE="$(printf '%s\n' "$PY_OUT" | grep '^PHASE_ID=' || true)"
PHASE_ID="${PHASE_ID_LINE#PHASE_ID=}"
emit_result ok add_phase "phase added" "phase_id=${PHASE_ID:-unknown}" "title=$TITLE"
