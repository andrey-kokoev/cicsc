#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MODEL="${ROOT_DIR}/control-plane/gates/gate-model.yaml"
SCHEMA="${ROOT_DIR}/control-plane/gates/gate-model.schema.json"
[[ -f "${MODEL}" ]] && [[ -f "${SCHEMA}" ]]
rg -q '^version:' "${MODEL}"
rg -q '^gates:' "${MODEL}"
node -e 'JSON.parse(require("node:fs").readFileSync(process.argv[1],"utf8"))' "${SCHEMA}"
echo "gate model check passed"
