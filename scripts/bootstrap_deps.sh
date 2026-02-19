#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODE="${1:-install}"

check_dep() {
  local module="$1"
  local base="$2"
  node -e "require.resolve(process.argv[1], { paths: [process.argv[2]] })" "$module" "$base" >/dev/null 2>&1
}

if [[ "$MODE" == "install" ]]; then
  npm --prefix "${ROOT_DIR}/adapters/sqlite" install --no-fund --no-audit
  npm --prefix "${ROOT_DIR}/adapters/postgres" install --no-fund --no-audit
  npm --prefix "${ROOT_DIR}/tests/harness-deps" install --no-fund --no-audit
  echo "dependency bootstrap install complete"
  exit 0
fi

if [[ "$MODE" == "check" ]]; then
  ok=0

  check_dep typescript "${ROOT_DIR}/adapters/sqlite" || { echo "missing typescript in adapters/sqlite; run ./scripts/bootstrap_deps.sh install"; ok=1; }
  check_dep typescript "${ROOT_DIR}/adapters/postgres" || { echo "missing typescript in adapters/postgres; run ./scripts/bootstrap_deps.sh install"; ok=1; }
  check_dep pg "${ROOT_DIR}/adapters/postgres" || { echo "missing pg in adapters/postgres; run ./scripts/bootstrap_deps.sh install"; ok=1; }
  check_dep pg-mem "${ROOT_DIR}/tests/harness-deps" || { echo "missing pg-mem in tests/harness-deps; run ./scripts/bootstrap_deps.sh install"; ok=1; }
  check_dep better-sqlite3 "${ROOT_DIR}/tests/harness-deps" || { echo "missing better-sqlite3 in tests/harness-deps; run ./scripts/bootstrap_deps.sh install"; ok=1; }

  if [[ "$ok" -ne 0 ]]; then
    exit 1
  fi

  echo "dependency bootstrap check passed"
  exit 0
fi

echo "usage: ./scripts/bootstrap_deps.sh [install|check]"
exit 2
