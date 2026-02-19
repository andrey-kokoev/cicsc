#!/usr/bin/env bash
#==============================================================================
# integrate.sh - FF-Only Collaboration Boundary
#
# This script implements the categorical constraint at the integration boundary.
# Workers operate unconstrained inside; integration enforces FF-property.
#
# Usage:
#   ./integrate.sh integrate <checkbox>    # Integrate phase (FF-constrained)
#   ./integrate.sh status                  # Show current state
#
# See:
#   - lean/Cicsc/Evolution/FFIntegration.lean (proofs)
#   - docs/foundations/category-model.md §11 (specification)
#   - docs/genesis/boundary-contraction.md (rationale)
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

integrate() {
    local checkbox="$1"
    
    echo "=== Integrate Phase ==="
    echo "Checkbox: $checkbox"
    
    current_branch=$(git branch --show-current)
    if [[ -z "$current_branch" ]]; then
        echo "ERROR: Not on a branch"
        exit 1
    fi
    
    echo "Current branch: $current_branch"
    
    main_hash=$(git rev-parse origin/main 2>/dev/null) || {
        echo "ERROR: origin/main not found"
        exit 1
    }
    
    merge_base=$(git merge-base HEAD origin/main 2>/dev/null) || {
        echo "ERROR: Cannot find merge base with origin/main"
        exit 1
    }
    
    if [[ "$merge_base" != "$main_hash" ]]; then
        echo "ERROR: Branch is not descendant of origin/main"
        echo "  merge_base: $merge_base"
        echo "  origin/main: $main_hash"
        echo ""
        echo "This is NOT an FF-morphism. Integration rejected."
        echo "Solution: Rebase onto origin/main first (but this is discouraged)"
        exit 1
    fi
    
    echo "FF-verified: Branch descends from origin/main"
    
    echo ""
    echo "Running validation gates..."
    if ! ./control-plane/check_gates.sh; then
        echo "ERROR: Gates failed"
        exit 1
    fi
    
    python3 - "$checkbox" "$(git rev-parse --short HEAD)" << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import complete_assignment

checkbox = sys.argv[1]
commit = sys.argv[2]

if complete_assignment(checkbox, commit):
    print(f"Updated {checkbox} to done")
else:
    print(f"Warning: {checkbox} not in assigned state")
PY
    
    echo ""
    echo "=== INTEGRATE COMPLETE ==="
    echo "Checkbox: $checkbox"
    echo "Integration: FF-morphism verified"
    echo "Evidence: $(git rev-parse HEAD)"
}

status() {
    echo "=== Collaboration Status ==="
    echo ""
    echo "Current branch: $(git branch --show-current)"
    echo "Main:           $(git rev-parse origin/main 2>/dev/null || echo 'not found')"
    echo "HEAD:           $(git rev-parse HEAD)"
    echo ""
    
    if git rev-parse HEAD >/dev/null 2>&1; then
        merge_base=$(git merge-base HEAD origin/main 2>/dev/null || echo "")
        main_hash=$(git rev-parse origin/main 2>/dev/null || echo "")
        
        if [[ "$merge_base" == "$main_hash" ]]; then
            echo "FF-status: VALID (FF-morphism exists)"
        else
            echo "FF-status: INVALID (not descendant of main)"
        fi
    fi
}

case "${1:-}" in
    integrate)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 integrate <checkbox>"
            exit 1
        fi
        integrate "$2"
        ;;
    status)
        status
        ;;
    *)
        echo "FF-Only Collaboration Boundary"
        echo ""
        echo "Usage:"
        echo "  $0 integrate <checkbox>    # Integrate phase (FF-constrained)"
        echo "  $0 status                  # Show current state"
        echo ""
        echo "See docs/genesis/boundary-contraction.md for rationale"
        exit 1
        ;;
esac
