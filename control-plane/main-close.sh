#!/usr/bin/env bash
#==============================================================================
# main-close.sh - Main-operator helper for closure flow
#
# Usage:
#   ./main-close.sh --branch feat/branch --checkbox CG1.19
#   ./main-close.sh --branch feat/branch              # infer checkbox
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

BRANCH=""
CHECKBOX=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --help|-h)
            echo "Usage: $0 --branch <branch> [--checkbox <id>]"
            exit 0
            ;;
        --branch) BRANCH="${2:-}"; shift 2 ;;
        --checkbox) CHECKBOX="${2:-}"; shift 2 ;;
        *) echo "Unknown arg: $1" >&2; exit 1 ;;
    esac
done

if [[ -z "$BRANCH" ]]; then
    echo "Usage: $0 --branch <branch> [--checkbox <id>]" >&2
    exit 1
fi

CURRENT_BRANCH="$(git branch --show-current)"
if [[ "$CURRENT_BRANCH" != "main" ]]; then
    echo "ERROR: main-close must run on branch 'main' (current: $CURRENT_BRANCH)" >&2
    exit 1
fi

echo "=== Main Close ==="
echo "Branch: $BRANCH"
if [[ -n "$CHECKBOX" ]]; then
    echo "Checkbox: $CHECKBOX"
else
    echo "Checkbox: infer from branch/commit context"
fi

echo ""
echo "[1/4] Fetch branch"
git fetch origin "$BRANCH"

echo "[2/4] Merge (FF-only)"
git merge --ff-only "origin/$BRANCH"

echo "[3/4] Integrate assignment"
if [[ -n "$CHECKBOX" ]]; then
    ./control-plane/integrate.sh integrate "$CHECKBOX"
else
    ./control-plane/integrate.sh integrate --from-branch "$BRANCH"
fi

echo "[4/4] Validate state"
./control-plane/validate.sh

echo ""
echo "Main-close complete."
