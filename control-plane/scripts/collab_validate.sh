#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

cd "${ROOT_DIR}"
./control-plane/scripts/validate_collab_model.sh
./control-plane/scripts/validate_cross_model.sh
echo "collaboration preflight validation passed"
