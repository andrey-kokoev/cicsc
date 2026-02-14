#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/validate_objective_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_capability_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_collab_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_execution_ledger_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_gate_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_cross_model.sh"
"${ROOT_DIR}/control-plane/scripts/validate_collab_status_output.sh"
echo "control-plane model checks passed"
