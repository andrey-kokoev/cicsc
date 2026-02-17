#!/usr/bin/env bash
#==============================================================================
# submit_collab_issue.sh - Report collaboration issues
#
# Usage:
#   ./submit_collab_issue.sh "issue description"
#==============================================================================

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ISSUE="${1:-}"

if [[ -z "$ISSUE" ]]; then
    echo "Usage: $0 \"issue description\""
    echo ""
    echo "Report collaboration issues to main agent."
    echo "Examples:"
    echo "  ./submit_collab_issue.sh \"BZ1.1 blocked - need spec document\""
    echo "  ./submit_collab_issue.sh \"Need clarification on BZ1.2 requirements\""
    exit 1
fi

echo "=============================================="
echo "  Submitting collaboration issue..."
echo "=============================================="
echo ""
echo "Issue: $ISSUE"
echo ""

# Create issue file
ISSUE_DIR=".collab-issues"
mkdir -p "$ISSUE_DIR"

TIMESTAMP=$(date +%Y%m%d-%H%M%S)
AGENT_NAME=$(whoami 2>/dev/null || echo "agent")
ISSUE_FILE="$ISSUE_DIR/${TIMESTAMP}-${AGENT_NAME}.md"

cat > "$ISSUE_FILE" << EOF
# Collaboration Issue

**Agent:** $AGENT_NAME
**Timestamp:** $(date -Iseconds)
**Status:** open

## Issue

$ISSUE

## Context

- Branch: $(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")
- Commit: $(git rev-parse --short HEAD 2>/dev/null || echo "unknown")

EOF

echo "✅ Issue submitted: $ISSUE_FILE"
echo ""
echo "Main agent will review and respond."
