#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/validate_model.py" \
  "${ROOT_DIR}/control-plane/execution/execution-ledger.yaml" \
  "${ROOT_DIR}/control-plane/execution/execution-ledger.schema.json"
echo "execution ledger model check passed"
