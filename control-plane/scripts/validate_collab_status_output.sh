#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/validate_collab_status_output.sh [--worktree <path>]
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"
status_json="$(./control-plane/scripts/collab_status.sh --worktree "${WORKTREE}" --json)"

python3 - "${ROOT_DIR}/control-plane/collaboration/collab-status-output.schema.json" "${status_json}" <<'PY'
import json
import sys
from pathlib import Path
import jsonschema

schema = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
doc = json.loads(sys.argv[2])
jsonschema.validate(instance=doc, schema=schema)
print("collab status output schema check passed")
PY
