#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MODEL="${ROOT_DIR}/control-plane/execution/execution-ledger.yaml"
SCHEMA="${ROOT_DIR}/control-plane/execution/execution-ledger.schema.json"
[[ -f "${MODEL}" ]] && [[ -f "${SCHEMA}" ]]
rg -q '^version:' "${MODEL}"
rg -q '^status_source_mode:' "${MODEL}"
rg -q '^phases:' "${MODEL}"
node -e 'JSON.parse(require("node:fs").readFileSync(process.argv[1],"utf8"))' "${SCHEMA}"
echo "execution ledger model check passed"
