#!/usr/bin/env bash
#==============================================================================
# onboard.sh - Onboard an agent to CICSC
#
# Usage:
#   ./onboard.sh --worker AGENT_GEMINI    # Worker onboarding
#   ./onboard.sh --main                   # Main agent onboarding
#==============================================================================

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ROLE="worker"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --main) ROLE="main"; shift ;;
        --worker) ROLE="worker"; shift ;;
        *) shift ;;
    esac
done

if [[ "$ROLE" == "main" ]]; then
    echo "=============================================="
    echo "  Welcome to CICSC (MAIN AGENT)"
    echo "=============================================="
    echo ""
    echo "Your role: Add work to ledger, maintain state"
    echo ""

    cat << 'GUIDE'
WORKFLOW:
=========
1. VALIDATE: ./control-plane/validate.sh
2. ADD WORK: ./control-plane/add_phase.sh --id CF --number N --title "T"
3. CHECKBOX: ./control-plane/add_checkbox.sh --milestone CF1 --checkbox "CF1.1:desc"
4. MERGE:    git fetch origin && git merge --ff-only origin/feat/branch
5. CLOSE:    ./control-plane/integrate.sh integrate CF1.1

That's it. Mechanistic core (autoassign.sh) assigns work to agents.

RULES:
======
- Just add work - don't dispatch
- Always validate after merges
- Use scripts: add_phase.sh, add_checkbox.sh

COMMANDS:
=========
| Task          | Command                                |
|---------------|----------------------------------------|
| Validate      | ./control-plane/validate.sh           |
| Add phase     | ./control-plane/add_phase.sh --id ...  |
| Add checkbox  | ./control-plane/add_checkbox.sh --... |
| Merge         | git merge --ff-only origin/feat/...   |
| Close         | ./control-plane/integrate.sh integrate CF1.1 |

GUIDE
    echo ""
    echo "Ready? Run:"
    echo "  ./control-plane/validate.sh"
else
    echo "=============================================="
    echo "  Welcome to CICSC (WORKER AGENT)"
    echo "=============================================="
    echo ""
    echo "Your role: Implement assigned work, push feature branches"
    echo ""

    cat << 'GUIDE'
WORKFLOW:
=========
1. SYNC:    git fetch origin && git rebase origin/main
2. ENV:     export AGENT_ID=AGENT_xxx
3. STANDBY: ./control-plane/standby.sh

The standby script polls every 5s. When work is assigned to you,
it outputs the task. Do the work, commit, push.

4. WORK:    Implement in worktree, commit
5. GATES:   ./control-plane/check_gates.sh
6. PUSH:    git push origin feat/description

RULES:
======
- Never edit state directly - use scripts
- Never commit to main - always feature branch
- Always run gates before pushing
- Push, then Main integrates to close checkbox

COMMANDS:
=========
| Task          | Command                                |
|---------------|----------------------------------------|
| Sync          | git fetch origin && git rebase origin/main |
| Standby       | export AGENT_ID=xxx && ./control-plane/standby.sh |
| Gates         | ./control-plane/check_gates.sh       |
| Push          | git push origin feat/branch-name     |

GUIDE

    echo ""
    echo "To start:"
    echo "  export AGENT_ID=YOUR_AGENT_NAME"
    echo "  ./control-plane/standby.sh"
fi
