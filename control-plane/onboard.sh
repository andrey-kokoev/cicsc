#!/usr/bin/env bash
#==============================================================================
# onboard.sh - Onboard an agent to CICSC
#
# Usage:
#   ./onboard.sh AGENT_KIMI
#==============================================================================

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGENT="${1:-}"

if [[ -z "$AGENT" ]]; then
    echo "Usage: $0 <agent_id>"
    echo ""
    echo "Onboard an agent to CICSC control-plane."
    exit 1
fi

echo "=============================================="
echo "  Welcome to CICSC, $AGENT!"
echo "=============================================="
echo ""

echo "Your role: AGENT worker"
echo ""
echo "Workflow:"
echo "  1. Fetch latest:  git fetch origin && git rebase origin/main"
echo "  2. Check inbox:   ./control-plane/inbox.sh $AGENT"
echo "  3. Claim work:    ./control-plane/claim.sh $AGENT"
echo "  4. Do the work:   (implement in your worktree)"
echo "  5. Run gates:     ./control-plane/check_gates.sh"
echo "  6. Complete:      ./control-plane/complete.sh <checkbox>"
echo "  7. Push branch:   git push origin <branch>"
echo ""
echo "Tips:"
echo "  - Worktrees auto-sync on inbox/claim/complete/check_gates"
echo "  - Use --no-sync to skip sync if needed"
echo "  - YAML files are read-only; use scripts to modify"
echo ""

# Show current assignments
echo "Your current assignments:"
./control-plane/inbox.sh "$AGENT"

echo ""
echo "Ready to work? Run:"
echo "  ./control-plane/claim.sh $AGENT"
