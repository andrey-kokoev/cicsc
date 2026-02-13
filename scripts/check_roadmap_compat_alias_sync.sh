#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./control-plane/scripts/generate_roadmap_compat.py > /dev/null

if ! git diff --exit-code -- ROADMAP.md >/dev/null; then
  echo "roadmap compatibility alias sync check failed: ROADMAP.md is out of sync" >&2
  echo "run: ./control-plane/scripts/generate_roadmap_compat.py" >&2
  exit 1
fi

echo "roadmap compatibility alias sync check passed"
