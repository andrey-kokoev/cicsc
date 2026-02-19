#!/usr/bin/env bash
#==============================================================================
# integrate.sh - FF-Only Collaboration Boundary
#
# Usage:
#   ./integrate.sh integrate <checkbox> --agent <AGENT_ID>
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"
source "$SCRIPT_DIR/output.sh"

usage() {
    cat <<USAGE
FF-Only Collaboration Boundary

Usage:
  $0 integrate <checkbox> --agent <AGENT_ID>
USAGE
}

integrate() {
    local checkbox="$1"
    local agent_id="$2"

    echo "=== Assignment Closure (Integrate Boundary) ==="
    echo "Checkbox: $checkbox"
    echo "Agent: $agent_id"

    local current_branch
    current_branch="$(git branch --show-current)"
    if [[ -z "$current_branch" ]]; then
        echo "ERROR: Not on a branch" >&2
        exit 1
    fi
    echo "Current branch: $current_branch"

    local main_hash
    main_hash="$(git rev-parse origin/main 2>/dev/null)" || {
        echo "ERROR: origin/main not found" >&2
        exit 1
    }

    local merge_base
    merge_base="$(git merge-base HEAD origin/main 2>/dev/null)" || {
        echo "ERROR: Cannot find merge base with origin/main" >&2
        exit 1
    }

    if [[ "$merge_base" != "$main_hash" ]]; then
        echo "ERROR: Branch is not descendant of origin/main" >&2
        echo "  merge_base: $merge_base" >&2
        echo "  origin/main: $main_hash" >&2
        echo "" >&2
        echo "This is NOT an FF-morphism. Integration rejected." >&2
        exit 1
    fi

    echo "FF-verified: Branch descends from origin/main"

    python3 - "$checkbox" "$(git rev-parse --short HEAD)" "$agent_id" <<'PY'
import sys
sys.path.insert(0, "control-plane")
from db import complete_assignment, get_assignment

checkbox = sys.argv[1]
commit = sys.argv[2]
agent = sys.argv[3]

assignment = get_assignment(checkbox)
if assignment is None or assignment.get("status") != "assigned":
    print(f"ERROR: Assignment {checkbox} is not actively assigned", file=sys.stderr)
    raise SystemExit(1)

owner = str(assignment.get("agent_ref") or "")
if owner != agent:
    print(
        f"ERROR: Assignment owner mismatch for {checkbox}: expected owner {owner}, got {agent}",
        file=sys.stderr,
    )
    raise SystemExit(3)

if complete_assignment(checkbox, commit, expected_agent=agent):
    print(f"Updated {checkbox} to done")
else:
    print(f"ERROR: Could not complete assignment for {checkbox}", file=sys.stderr)
    raise SystemExit(1)
PY

    echo ""
    echo "=== ASSIGNMENT CLOSE COMPLETE ==="
    echo "Checkbox: $checkbox"
    echo "Integration: FF-morphism verified"
    echo "Evidence: $(git rev-parse HEAD)"
    emit_result ok integrate "integration complete" "checkbox=$checkbox" "commit=$(git rev-parse --short HEAD)"
}

case "${1:-}" in
    integrate)
        shift
        checkbox=""
        agent_id=""
        while [[ $# -gt 0 ]]; do
            case "$1" in
                --agent)
                    agent_id="${2:-}"
                    shift 2
                    ;;
                --help|-h)
                    usage
                    exit 0
                    ;;
                *)
                    if [[ -n "$checkbox" ]]; then
                        echo "ERROR: Unexpected extra argument '$1'" >&2
                        usage >&2
                        exit 1
                    fi
                    checkbox="$1"
                    shift
                    ;;
            esac
        done

        if [[ -z "$checkbox" || -z "$agent_id" ]]; then
            echo "ERROR: integrate requires <checkbox> and --agent <AGENT_ID>" >&2
            usage >&2
            exit 1
        fi

        integrate "$checkbox" "$agent_id"
        ;;
    --help|-h)
        usage
        exit 0
        ;;
    *)
        usage >&2
        exit 1
        ;;
esac
