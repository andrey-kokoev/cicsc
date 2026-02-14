#!/usr/bin/env bash
set -euo pipefail

EXPECTED_ROOT="${1:-}"
if [[ -z "${EXPECTED_ROOT}" ]]; then
  echo "missing expected root argument" >&2
  exit 2
fi

if [[ "${PWD}" != "${EXPECTED_ROOT}" ]]; then
  ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
  "${ROOT_DIR}/control-plane/scripts/collab_root_hint.sh" "${EXPECTED_ROOT}"
  exit 1
fi
