#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

cd "${ROOT_DIR}"
./control-plane/scripts/validate_collab_model.sh
./control-plane/scripts/validate_cross_model.sh
echo "collaboration preflight validation passed"
