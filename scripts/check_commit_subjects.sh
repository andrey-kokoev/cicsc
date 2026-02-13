#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

BASE_REF="${1:-HEAD~40}"
HEAD_REF="${2:-HEAD}"

if ! git rev-parse --verify --quiet "$BASE_REF" >/dev/null; then
  echo "base ref not found: $BASE_REF" >&2
  exit 2
fi
if ! git rev-parse --verify --quiet "$HEAD_REF" >/dev/null; then
  echo "head ref not found: $HEAD_REF" >&2
  exit 2
fi

mapfile -t COMMITS < <(git rev-list --no-merges "${BASE_REF}..${HEAD_REF}")

allowed_subject() {
  local s="$1"

  [[ "$s" =~ ^phase[0-9]+[[:space:]][a-z]{1,2}[0-9]+(\.[0-9]+)?:[[:space:]].+ ]] && return 0
  [[ "$s" =~ ^(docs|chore|ci|test|refactor|governance|release)(/[a-z0-9._-]+)?:[[:space:]].+ ]] && return 0
  [[ "$s" =~ ^Merge[[:space:]].+ ]] && return 0
  [[ "$s" =~ ^Revert[[:space:]].+ ]] && return 0
  return 1
}

fail=0
for c in "${COMMITS[@]}"; do
  subject="$(git show -s --format=%s "$c")"
  if ! allowed_subject "$subject"; then
    echo "invalid subject: $c $subject" >&2
    fail=1
  fi
done

if [[ "$fail" -ne 0 ]]; then
  echo "commit subject policy check failed" >&2
  exit 1
fi

echo "commit subject policy check passed"
