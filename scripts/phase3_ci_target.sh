#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "${ROOT_DIR}"

./scripts/node_test.sh tests/oracle/replay-and-constraints.test.ts
./scripts/node_test.sh tests/conformance/sqlite-lowering-vs-oracle.test.ts
./scripts/node_test.sh tests/conformance/sqlite-exec-vs-oracle-smoke.test.ts
./scripts/node_test.sh tests/conformance/sqlite-random-vs-oracle.test.ts
./scripts/node_test.sh tests/core/view-row-policy-typecheck.test.ts
