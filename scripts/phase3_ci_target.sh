#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOADER="${ROOT_DIR}/tests/harness/ts-extension-loader.mjs"

cd "${ROOT_DIR}"

node --loader "${LOADER}" --test tests/oracle/replay-and-constraints.test.ts
node --loader "${LOADER}" --test tests/conformance/sqlite-lowering-vs-oracle.test.ts
node --loader "${LOADER}" --test tests/core/view-row-policy-typecheck.test.ts
