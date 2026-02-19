#!/usr/bin/env bash
#==============================================================================
# add_milestone.sh - Add milestone to an existing phase
#
# Usage:
#   ./add_milestone.sh --phase CG --title "Milestone title"
#   ./add_milestone.sh --phase CG --id CG2 --title "Milestone title"
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

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

PHASE_ID=""
MILESTONE_ID=""
TITLE=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --help|-h)
            echo "Usage: $0 --phase <phase_id> [--id <milestone_id>] --title <title>"
            exit 0
            ;;
        --phase) PHASE_ID="$2"; shift 2 ;;
        --id) MILESTONE_ID="$2"; shift 2 ;;
        --title) TITLE="$2"; shift 2 ;;
        *) echo "Unknown: $1" >&2; exit 1 ;;
    esac
done

if [[ -z "$PHASE_ID" || -z "$TITLE" ]]; then
    echo "Usage: $0 --phase <phase_id> [--id <milestone_id>] --title <title>" >&2
    exit 1
fi

python3 - "$PHASE_ID" "$MILESTONE_ID" "$TITLE" << 'PY'
import re
import sys
sys.path.insert(0, "control-plane")
from db import add_milestone, get_phase, get_milestones_by_phase

phase_id = sys.argv[1].upper()
milestone_id = sys.argv[2].upper()
title = sys.argv[3]

if get_phase(phase_id) is None:
    print(f"ERROR: Phase {phase_id} not found", file=sys.stderr)
    sys.exit(1)

existing = {m["id"].upper() for m in get_milestones_by_phase(phase_id)}

if not milestone_id:
    used = set()
    pattern = re.compile(rf"^{re.escape(phase_id)}(\d+)$")
    for mid in existing:
        m = pattern.match(mid)
        if m:
            used.add(int(m.group(1)))
    n = 1
    while n in used:
        n += 1
    milestone_id = f"{phase_id}{n}"

if not re.fullmatch(r"[A-Z]{1,3}\d+", milestone_id):
    print(f"ERROR: Invalid milestone id format: {milestone_id}", file=sys.stderr)
    sys.exit(1)

if not milestone_id.startswith(phase_id):
    print(
        f"ERROR: Milestone id {milestone_id} must start with phase id {phase_id}",
        file=sys.stderr,
    )
    sys.exit(1)

if milestone_id in existing:
    print(f"ERROR: Milestone {milestone_id} already exists", file=sys.stderr)
    sys.exit(1)

add_milestone(milestone_id, phase_id, title)
print(f"Added milestone {milestone_id} to phase {phase_id}")
print(f"MILESTONE_ID={milestone_id}")
PY
