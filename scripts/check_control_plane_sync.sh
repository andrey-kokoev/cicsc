#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./control-plane/validate.sh > /dev/null
./scripts/run_gate_model.sh --print-plan > /dev/null

echo "control-plane sync check passed"
