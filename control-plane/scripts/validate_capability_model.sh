#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MODEL="${ROOT_DIR}/control-plane/capabilities/capability-model.yaml"
SCHEMA="${ROOT_DIR}/control-plane/capabilities/capability-model.schema.json"
[[ -f "${MODEL}" ]] && [[ -f "${SCHEMA}" ]]
rg -q '^version:' "${MODEL}"
rg -q '^capabilities:' "${MODEL}"
node -e 'JSON.parse(require("node:fs").readFileSync(process.argv[1],"utf8"))' "${SCHEMA}"
echo "capability model check passed"
