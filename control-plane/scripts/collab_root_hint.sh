#!/usr/bin/env bash
set -euo pipefail

EXPECTED_ROOT="${1:-}"
if [[ -z "${EXPECTED_ROOT}" ]]; then
  echo "missing expected root argument" >&2
  exit 2
fi

echo "error: run this command from repository root: ${EXPECTED_ROOT}" >&2
echo "hint: cd ${EXPECTED_ROOT}" >&2
