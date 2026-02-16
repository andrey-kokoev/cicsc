#!/usr/bin/env bash
#==============================================================================
# integrate.sh - FF-Only Collaboration Boundary
#
# This script implements the categorical constraint at the integration boundary.
# Workers operate unconstrained inside; integration enforces FF-property.
#
# Usage:
#   ./integrate.sh claim <agent>           # Claim phase (unconstrained)
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

#------------------------------------------------------------------------------
# Phase 1: Claim - Create branch (UNCONSTRAINED)
#------------------------------------------------------------------------------
claim() {
    local agent="$1"
    
    echo "=== Claim Phase ==="
    echo "Agent: $agent"
    
    # Fetch latest main
    echo "Fetching origin/main..."
    git fetch origin main 2>/dev/null || true
    
    # Update assignments.yaml to in_progress
    python3 - "$agent" << 'PY'
import yaml
import sys
from datetime import datetime

agent = sys.argv[1]
assignments = yaml.safe_load(open("control-plane/assignments.yaml"))

claimed = []
for a in assignments.get("assignments", []):
    if a.get("agent_ref") == agent and a.get("status") == "open":
        a["status"] = "in_progress"
        a["started_at"] = datetime.now().isoformat() + "Z"
        claimed.append(a["checkbox_ref"])

if claimed:
    open("control-plane/assignments.yaml", "w").write(yaml.dump(assignments, sort_keys=False))
    print(f"Claimed: {', '.join(claimed)}")
else:
    print("No open assignments to claim")
PY
    
    echo ""
    echo "CLAIM COMPLETE - Work unconstrained until integrate"
    echo "Run './integrate.sh integrate <checkbox>' when ready"
}

#------------------------------------------------------------------------------
# Phase 2: Integrate - FF-Only Merge (CONSTRAINED)
#------------------------------------------------------------------------------
integrate() {
    local checkbox="$1"
    
    echo "=== Integrate Phase ==="
    echo "Checkbox: $checkbox"
    
    # Get current branch and verify it's the worktree
    current_branch=$(git branch --show-current)
    if [[ -z "$current_branch" ]]; then
        echo "ERROR: Not on a branch"
        exit 1
    fi
    
    echo "Current branch: $current_branch"
    
    # Verify we're branched from main
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
    
    # Run validation gates before integration
    echo ""
    echo "Running validation gates..."
    if ! ./control-plane/check_gates.sh; then
        echo "ERROR: Gates failed"
        exit 1
    fi
    
    # Update checkbox status in assignments.yaml
    python3 - "$checkbox" << 'PY'
import yaml
import sys
from datetime import datetime

checkbox = sys.argv[1]
assignments = yaml.safe_load(open("control-plane/assignments.yaml"))

updated = False
for a in assignments.get("assignments", []):
    if a.get("checkbox_ref") == checkbox:
        a["status"] = "done"
        a["completed_at"] = datetime.now().isoformat() + "Z"
        updated = True

if updated:
    open("control-plane/assignments.yaml", "w").write(yaml.dump(assignments, sort_keys=False))
    print(f"Updated {checkbox} to done")
else:
    print(f"Warning: {checkbox} not found in assignments")
PY
    
    # Stage assignments.yaml
    git add control-plane/assignments.yaml
    
    # Create integration commit
    local commit_msg="integrate: $checkbox via FF-merge

This integration satisfies the FF-morphism constraint.
See lean/Cicsc/Evolution/FFIntegration.lean for proofs."
    
    if git diff --cached --quiet; then
        echo "No changes to commit"
    else
        git commit -m "$commit_msg"
    fi
    
    # FF-only merge into main
    echo ""
    echo "Attempting FF-merge into origin/main..."
    if git merge --ff-only -m "merge: $checkbox" origin/main 2>/dev/null; then
        echo "FF-merge succeeded"
    else
        # This should not happen if FF-verification passed
        echo "ERROR: FF-merge failed unexpectedly"
        echo "This indicates a violation of categorical constraints"
        exit 1
    fi
    
    # Push to origin
    echo ""
    echo "Pushing to origin..."
    git push origin main
    
    echo ""
    echo "=== INTEGRATE COMPLETE ==="
    echo "Checkbox: $checkbox"
    echo "Integration: FF-morphism verified"
    echo "Evidence: $(git rev-parse HEAD)"
}

#------------------------------------------------------------------------------
# Status: Show current state
#------------------------------------------------------------------------------
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

#------------------------------------------------------------------------------
# Main dispatch
#------------------------------------------------------------------------------
case "${1:-}" in
    claim)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 claim <agent>"
            exit 1
        fi
        claim "$2"
        ;;
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
        echo "  $0 claim <agent>           # Claim phase (unconstrained)"
        echo "  $0 integrate <checkbox>    # Integrate phase (FF-constrained)"
        echo "  $0 status                  # Show current state"
        echo ""
        echo "See docs/genesis/boundary-contraction.md for rationale"
        exit 1
        ;;
esac
