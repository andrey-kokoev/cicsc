#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/validate_objective_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_capability_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_execution_ledger_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_gate_model.sh"
echo "control-plane model checks passed"
