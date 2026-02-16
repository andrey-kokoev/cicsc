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
    echo "Your role: Orchestrate workers, manage dispatch"
    echo ""

    # Inline main guide
    cat << 'GUIDE'
WORKFLOW (read carefully):
=======================
1. VALIDATE: ./control-plane/validate.sh
2. CHECK:    grep status open control-plane/execution-ledger.yaml
3. ADD:      ./control-plane/add_phase.sh --id BZ --number N --title "T"
4. DISPATCH: ./control-plane/dispatch.sh --checkbox BZ1.1 --agent AGENT_KIMI
5. COMMIT:   git add control-plane/ && git commit -m "dispatch: ..."
6. PUSH:     git push origin main
7. MONITOR:  ./control-plane/inbox.sh AGENT_NAME
8. MERGE:    git fetch origin && git merge --ff-only origin/feat/branch

RULES (non-negotiable):
======================
- NEVER edit YAML directly - use scripts
- ALWAYS validate after merges
- DISPATCH smallest adjacent steps
- Use scripts: add_phase.sh, add_checkbox.sh, dispatch.sh

COMMON COMMANDS:
================
| Task          | Command                                |
|---------------|----------------------------------------|
| Validate      | ./control-plane/validate.sh           |
| Add phase     | ./control-plane/add_phase.sh --id ...  |
| Add checkbox  | ./control-plane/add_checkbox.sh --... |
| Dispatch      | ./control-plane/dispatch.sh --...     |
| Monitor       | ./control-plane/inbox.sh AGENT_NAME   |
| Merge         | git merge --ff-only origin/feat/...   |

GUIDE
    echo ""
    echo "Ready? Run:"
    echo "  ./control-plane/validate.sh"
else
    echo "=============================================="
    echo "  Welcome to CICSC, $AGENT!"
    echo "=============================================="
    echo ""

    echo "Your role: AGENT worker - implement assigned work"
    echo ""

    # Inline worker guide
    cat << 'GUIDE'
WORKFLOW (read carefully):
=======================
1. SYNC:     git fetch origin && git rebase origin/main
2. INBOX:    ./control-plane/inbox.sh AGENT_NAME
3. CLAIM:    ./control-plane/claim.sh AGENT_NAME   <- REQUIRED BEFORE WORK
4. WORK:     Implement in worktree, commit
5. GATES:    ./control-plane/check_gates.sh         <- REQUIRED BEFORE COMPLETE
6. COMPLETE: ./control-plane/complete.sh CHECKBOX   <- REQUIRED WHEN DONE
7. PUSH:     git push origin feat/description

RULES (non-negotiable):
======================
- NEVER edit YAML files directly - use scripts
- NEVER commit to main - always feature branch
- ALWAYS run gates before completing
- ALWAYS complete work with complete.sh
- ALWAYS sync before starting (rebase origin/main)

COMMON COMMANDS:
================
| Task          | Command                                |
|---------------|----------------------------------------|
| Sync          | git fetch origin && git rebase origin/main |
| Claim         | ./control-plane/claim.sh AGENT_NAME  |
| Gates         | ./control-plane/check_gates.sh       |
| Complete      | ./control-plane/complete.sh BZ1.1     |
| Push branch   | git push origin feat/branch-name     |

GUIDE
    echo ""

    # Show current assignments and auto-claim
    echo "Your assignments:"
    ./control-plane/inbox.sh "$AGENT"

    echo ""
    echo "Auto-claiming..."
    ./control-plane/claim.sh "$AGENT"

    echo ""
    echo "Now implement. Run gates when ready:"
    echo "  ./control-plane/check_gates.sh"
fi
