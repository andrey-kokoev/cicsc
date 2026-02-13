#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/validate_model.py" \
  "${ROOT_DIR}/control-plane/capabilities/capability-model.yaml" \
  "${ROOT_DIR}/control-plane/capabilities/capability-model.schema.json"
echo "capability model check passed"
