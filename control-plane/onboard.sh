#!/usr/bin/env bash
#==============================================================================
# onboard.sh - Onboard an agent to CICSC
#
# Usage:
#   ./onboard.sh AGENT_KIMI          # Worker onboarding
#   ./onboard.sh --main AGENT_MAIN   # Main agent onboarding
#==============================================================================

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ROLE="worker"
AGENT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --main) ROLE="main"; shift ;;
        *) AGENT="$1"; shift ;;
    esac
done

if [[ -z "$AGENT" ]]; then
    echo "Usage: $0 [--main] <agent_id>"
    echo ""
    echo "Onboard an agent to CICSC control-plane."
    echo "  --main    Onboard as main agent (not worker)"
    exit 1
fi

if [[ "$ROLE" == "main" ]]; then
    echo "=============================================="
    echo "  Welcome to CICSC, $AGENT (MAIN AGENT)!"
    echo "=============================================="
    echo ""
    echo "Your role: AGENT main - orchestrate workers"
    echo ""
    echo "See: AGENTS_MAIN.md for full guide"
    echo ""
    echo "Quick workflow:"
    echo "  1. Validate:    ./control-plane/validate.sh"
    echo "  2. Add work:   ./control-plane/add_phase.sh --id BZ ..."
    echo "  3. Dispatch:    ./control-plane/dispatch.sh --checkbox BZ1.1 --agent AGENT_KIMI"
    echo "  4. Commit:     git add control-plane/ && git commit -m 'dispatch: ...'"
    echo "  5. Monitor:    ./control-plane/inbox.sh"
    echo "  6. Merge:      git merge --ff-only origin/feat/..."
    echo "  7. Push:       git push origin main"
    echo ""
    echo "Ready? Run:"
    echo "  ./control-plane/validate.sh"
else
    echo "=============================================="
    echo "  Welcome to CICSC, $AGENT!"
    echo "=============================================="
    echo ""
    echo "Your role: AGENT worker"
    echo ""
    echo "See: AGENTS_WORKER.md for full guide"
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

    # Show current assignments and auto-claim
    echo "Your current assignments:"
    ./control-plane/inbox.sh "$AGENT"

    echo ""
    echo "Auto-claiming all open assignments..."
    ./control-plane/claim.sh "$AGENT"

    echo ""
    echo "Ready to work? Run:"
    echo "  ./control-plane/check_gates.sh"
fi
