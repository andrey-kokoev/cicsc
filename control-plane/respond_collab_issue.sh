#!/usr/bin/env bash
#==============================================================================
# respond_collab_issue.sh - Respond to a collaboration issue
#
# Usage:
#   ./respond_collab_issue.sh <issue-file> "response text"
#   ./respond_collab_issue.sh .collab-issues/20260216-120000-agent.md "Fixed in commit xyz"
#==============================================================================

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ISSUE_FILE="${1:-}"
RESPONSE="${2:-}"

if [[ -z "$ISSUE_FILE" || -z "$RESPONSE" ]]; then
    echo "Usage: $0 <issue-file> \"response\""
    echo ""
    echo "Examples:"
    echo "  ./respond_collab_issue.sh .collab-issues/20260216-120000-agent.md \"Fixed in commit abc123\""
    echo "  ./respond_collab_issue.sh .collab-issues/20260216-120000-andrey.md \"Working on it\""
    echo ""
    echo "Open issues:"
    ./control-plane/get_open_collab_issues.sh
    exit 1
fi

if [[ ! -f "$ISSUE_FILE" ]]; then
    echo "ERROR: Issue file not found: $ISSUE_FILE"
    exit 1
fi

echo "=============================================="
echo "  Responding to issue..."
echo "=============================================="
echo ""
echo "Issue: $ISSUE_FILE"
echo "Response: $RESPONSE"
echo ""

# Add response to issue
cat >> "$ISSUE_FILE" << EOF

## Response

**Responder:** main agent
**Timestamp:** $(date -Iseconds)

$RESPONSE

EOF

echo "✅ Response added to issue."
