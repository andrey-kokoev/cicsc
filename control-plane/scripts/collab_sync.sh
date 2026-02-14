#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

cd "${ROOT_DIR}"
./control-plane/scripts/generate_views.sh
./control-plane/scripts/validate_all.sh
echo "collab sync completed"
