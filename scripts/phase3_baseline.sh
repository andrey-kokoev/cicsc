#!/usr/bin/env bash
set -u

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

pass_count=0
fail_count=0

run_check() {
  local name="$1"
  shift

  echo "==> ${name}"
  if "$@"; then
    echo "PASS: ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL: ${name}"
    fail_count=$((fail_count + 1))
  fi
  echo
}

run_check "lean build" bash -lc "cd '${ROOT_DIR}/lean' && lake build"
run_check "adapter sqlite typecheck" bash -lc "cd '${ROOT_DIR}' && npm --prefix adapters/sqlite run check"
run_check "adapter postgres typecheck" bash -lc "cd '${ROOT_DIR}' && npm --prefix adapters/postgres run check"
run_check "oracle test: replay and constraints" bash -lc "cd '${ROOT_DIR}' && node --test tests/oracle/replay-and-constraints.test.ts"
run_check "conformance test: sqlite exec vs oracle" bash -lc "cd '${ROOT_DIR}' && node --test tests/conformance/sqlite-exec-vs-oracle.test.ts"
run_check "typechecker negative: view row policy" bash -lc "cd '${ROOT_DIR}' && node --test tests/core/view-row-policy-typecheck.test.ts"

echo "Summary: ${pass_count} passed, ${fail_count} failed"

if [[ ${fail_count} -ne 0 ]]; then
  exit 1
fi
