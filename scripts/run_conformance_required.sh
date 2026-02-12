#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROFILE="${1:-default}"
MATRIX_PATH="${ROOT_DIR}/tests/conformance/required-matrix.json"

cd "${ROOT_DIR}"
./scripts/check_conformance_matrix.sh

mapfile -t TEST_FILES < <(
  node - "${MATRIX_PATH}" "${PROFILE}" <<'NODE'
const fs = require("node:fs")

const matrixPath = process.argv[2]
const profile = process.argv[3]
const json = JSON.parse(fs.readFileSync(matrixPath, "utf-8"))

for (const suite of json.suites) {
  if (!suite.required) continue
  if (suite.ci_profile !== profile) continue
  for (const tf of suite.test_files) {
    console.log(tf)
  }
}
NODE
)

if [[ "${#TEST_FILES[@]}" -eq 0 ]]; then
  echo "no required conformance suites for profile '${PROFILE}'" >&2
  exit 1
fi

for tf in "${TEST_FILES[@]}"; do
  ./scripts/node_test.sh "${tf}"
done
