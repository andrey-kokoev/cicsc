#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ "$#" -lt 1 ]]; then
  echo "usage: ./scripts/node_test.sh <test-file> [<test-file> ...]" >&2
  exit 2
fi

node --loader "${ROOT_DIR}/tests/harness/ts-extension-loader.mjs" --test "$@"
