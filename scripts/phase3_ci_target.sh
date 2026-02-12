#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "${ROOT_DIR}"

./scripts/node_test.sh tests/oracle/replay-and-constraints.test.ts
./scripts/run_conformance_required.sh default
./scripts/node_test.sh tests/core/view-row-policy-typecheck.test.ts
./scripts/check_v4_refs.sh
