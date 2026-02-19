#!/usr/bin/env bash
#==============================================================================
# plan_work.sh - One-shot work planning helper
#
# Composes add_phase + add_milestone + add_checkbox while preserving
# low-level scripts for explicit/manual workflows.
#
# Usage:
#   ./plan_work.sh \
#     --phase-title "Intent Plane Hardening" \
#     --milestone-title "First Cut" \
#     --checkbox "Define acceptance policy" \
#     --checkbox "Add scenario tests"
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

PHASE_ID=""
PHASE_NUMBER=""
PHASE_TITLE=""
PHASE_DESCRIPTION=""
MILESTONE_ID=""
MILESTONE_TITLE=""
CHECKBOX_INPUTS=()

usage() {
    cat <<EOF
Usage: $0 --phase-title <title> --milestone-title <title> --checkbox <desc-or-id:desc> [options]

Options:
  --phase-id <id>            Explicit phase id (optional)
  --phase-number <num>       Explicit phase number (optional)
  --phase-title <title>      Phase title (required)
  --phase-description <desc> Phase description (optional)
  --milestone-id <id>        Explicit milestone id (optional)
  --milestone-title <title>  Milestone title (required)
  --checkbox <value>         Checkbox text. If 'id:desc', keep id; if just text, auto-id.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --help|-h) usage; exit 0 ;;
        --phase-id) PHASE_ID="${2:-}"; shift 2 ;;
        --phase-number) PHASE_NUMBER="${2:-}"; shift 2 ;;
        --phase-title) PHASE_TITLE="${2:-}"; shift 2 ;;
        --phase-description) PHASE_DESCRIPTION="${2:-}"; shift 2 ;;
        --milestone-id) MILESTONE_ID="${2:-}"; shift 2 ;;
        --milestone-title) MILESTONE_TITLE="${2:-}"; shift 2 ;;
        --checkbox)
            CHECKBOX_INPUTS+=("${2:-}")
            shift 2
            ;;
        *)
            echo "Unknown arg: $1" >&2
            usage >&2
            exit 1
            ;;
    esac
done

if [[ -z "$PHASE_TITLE" || -z "$MILESTONE_TITLE" || ${#CHECKBOX_INPUTS[@]} -eq 0 ]]; then
    usage >&2
    exit 1
fi

phase_args=(--title "$PHASE_TITLE")
if [[ -n "$PHASE_ID" ]]; then
    phase_args+=(--id "$PHASE_ID")
fi
if [[ -n "$PHASE_NUMBER" ]]; then
    phase_args+=(--number "$PHASE_NUMBER")
fi
if [[ -n "$PHASE_DESCRIPTION" ]]; then
    phase_args+=(--description "$PHASE_DESCRIPTION")
fi

phase_out="$("$SCRIPT_DIR/add_phase.sh" "${phase_args[@]}")"
echo "$phase_out"

if [[ -z "$PHASE_ID" ]]; then
    PHASE_ID="$(printf '%s\n' "$phase_out" | awk -F= '/^PHASE_ID=/{print $2; exit}')"
fi

if [[ -z "$PHASE_ID" ]]; then
    echo "ERROR: Failed to determine phase id from add_phase output" >&2
    exit 1
fi

milestone_args=(--phase "$PHASE_ID" --title "$MILESTONE_TITLE")
if [[ -n "$MILESTONE_ID" ]]; then
    milestone_args+=(--id "$MILESTONE_ID")
fi

milestone_out="$("$SCRIPT_DIR/add_milestone.sh" "${milestone_args[@]}")"
echo "$milestone_out"

if [[ -z "$MILESTONE_ID" ]]; then
    MILESTONE_ID="$(printf '%s\n' "$milestone_out" | awk -F= '/^MILESTONE_ID=/{print $2; exit}')"
fi

if [[ -z "$MILESTONE_ID" ]]; then
    echo "ERROR: Failed to determine milestone id from add_milestone output" >&2
    exit 1
fi

NEXT_SUFFIX="$(
python3 - "$MILESTONE_ID" << 'PY'
import re
import sys
sys.path.insert(0, "control-plane")
from db import get_checkboxes_by_milestone

mid = sys.argv[1]
max_suffix = 0
for cb in get_checkboxes_by_milestone(mid):
    m = re.match(r".*\.(\d+)$", str(cb.get("id", "")))
    if m:
        n = int(m.group(1))
        if n > max_suffix:
            max_suffix = n
print(max_suffix + 1)
PY
)"

cb_args=(--milestone "$MILESTONE_ID")
suffix="$NEXT_SUFFIX"
for raw in "${CHECKBOX_INPUTS[@]}"; do
    if [[ "$raw" == *:* ]]; then
        cb_args+=(--checkbox "$raw")
    else
        cb_id="${MILESTONE_ID}.${suffix}"
        cb_args+=(--checkbox "${cb_id}:${raw}")
        suffix=$((suffix + 1))
    fi
done

cb_out="$("$SCRIPT_DIR/add_checkbox.sh" "${cb_args[@]}")"
echo "$cb_out"
echo "{\"status\":\"ok\",\"command\":\"plan_work\",\"phase_id\":\"$PHASE_ID\",\"milestone_id\":\"$MILESTONE_ID\"}"
