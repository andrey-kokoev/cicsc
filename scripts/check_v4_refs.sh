#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DOC="${ROOT_DIR}/LEAN_KERNEL_V4.md"

checked_ids=$(
  grep -E '^- \[x\] K4\.[0-9]+\.[0-9]+' "${DOC}" \
    | sed -E 's/^- \[x\] (K4\.[0-9]+\.[0-9]+).*/\1/' \
    | sort -u
)

missing=0
for id in ${checked_ids}; do
  if ! grep -qE "^- \`${id}\`:" "${DOC}"; then
    echo "Missing completion reference for checked item: ${id}" >&2
    missing=1
  fi
done

if [[ ${missing} -ne 0 ]]; then
  exit 1
fi

echo "v4 reference check passed."
