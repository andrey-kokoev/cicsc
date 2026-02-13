#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./control-plane/scripts/validate_all.sh
./control-plane/scripts/generate_views.sh > /dev/null

shopt -s nullglob
files=(control-plane/views/*.generated.md)
if [[ ${#files[@]} -eq 0 ]]; then
  echo "control-plane sync check failed: no generated view files found" >&2
  exit 1
fi

for f in "${files[@]}"; do
  if ! git ls-files --error-unmatch "${f}" >/dev/null 2>&1; then
    echo "control-plane sync check failed: generated view is not tracked: ${f}" >&2
    exit 1
  fi
done

if ! git diff --exit-code -- "${files[@]}" >/dev/null; then
  echo "control-plane sync check failed: generated views are out of sync" >&2
  echo "run: ./control-plane/scripts/generate_views.sh" >&2
  exit 1
fi

echo "control-plane sync check passed"
