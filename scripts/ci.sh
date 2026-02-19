#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "${ROOT_DIR}"

# Default automation validation entrypoint.
./scripts/bootstrap_deps.sh check
./scripts/ci_target.sh
