#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./scripts/check_roadmap_integrity.sh
./scripts/check_phase_views_sync.sh
./scripts/check_checkbox_commit_evidence.sh
./scripts/check_workflow_single_source.sh
./scripts/check_control_plane_sync.sh
./scripts/check_roadmap_structure_sync.sh
./scripts/check_status_source_mode.sh
./scripts/check_generated_artifacts_policy.sh
./scripts/check_category_model_conformance.sh

echo "canonical execution model checks passed"
