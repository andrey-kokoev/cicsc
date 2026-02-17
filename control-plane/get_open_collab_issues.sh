#!/usr/bin/env bash
#==============================================================================
# get_open_collab_issues.sh - View open collaboration issues
#
# Usage:
#   ./get_open_collab_issues.sh
#==============================================================================

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ISSUE_DIR=".collab-issues"

if [[ ! -d "$ISSUE_DIR" ]]; then
    echo "No collaboration issues found."
    exit 0
fi

echo "=============================================="
echo "  Open Collaboration Issues"
echo "=============================================="
echo ""

count=0
for issue in "$ISSUE_DIR"/*.md; do
    [[ -e "$issue" ]] || continue
    
    # Check if still open (not resolved)
    if grep -q "Status:.*resolved\|Status:.*closed" "$issue" 2>/dev/null; then
        continue
    fi
    
    count=$((count + 1))
    echo "--- Issue $count ---"
    cat "$issue"
    echo ""
done

if [[ $count -eq 0 ]]; then
    echo "No open issues."
else
    echo "Total open: $count"
fi
