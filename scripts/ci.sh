#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "${ROOT_DIR}"

# Default automation validation entrypoint.
./scripts/phase3_bootstrap.sh check
./scripts/phase3_ci_target.sh
