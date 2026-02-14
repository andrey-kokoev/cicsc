#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./scripts/run_gate_model.sh || {
  echo "canonical execution model check failed" >&2
  echo "hint: run ./control-plane/scripts/collab_sync.sh" >&2
  echo "hint: then re-run ./scripts/check_canonical_execution_model.sh" >&2
  exit 1
}

echo "canonical execution model checks passed"
