#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Auto-sync if on worktree and behind main
needs_sync() {
    local local_head remote_head
    local_head=$(git rev-parse HEAD)
    remote_head=$(git rev-parse origin/main 2>/dev/null) || return 1
    [[ "$local_head" != "$remote_head" ]]
}

if needs_sync 2>/dev/null; then
    echo "⚠ Worktree is behind origin/main. Fetching..."
    git fetch origin
    git rebase origin/main
    echo "  ✅ Synced"
fi

echo "Running gate checks..."

# Run canonical execution model check
if [[ -x scripts/check_canonical_execution_model.sh ]]; then
    echo "  Running check_canonical_execution_model.sh..."
    if ! ./scripts/check_canonical_execution_model.sh; then
        echo "  FAILED: check_canonical_execution_model.sh" >&2
        exit 1
    fi
fi

echo "All gates passed"
