#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

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
