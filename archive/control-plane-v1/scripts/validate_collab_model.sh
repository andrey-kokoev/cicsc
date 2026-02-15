#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/validate_model.py" \
  "${ROOT_DIR}/control-plane/collaboration/collab-model.yaml" \
  "${ROOT_DIR}/control-plane/collaboration/collab-model.schema.json"
echo "collaboration model check passed"
