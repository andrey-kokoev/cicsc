#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MATRIX_PATH="${ROOT_DIR}/tests/conformance/postgres-exec-matrix.json"
SCOPE_PATH="${ROOT_DIR}/tests/conformance/postgres-supported-scope.json"

node <<'NODE' "${MATRIX_PATH}" "${SCOPE_PATH}"
const fs = require("node:fs")
const matrixPath = process.argv[1]
const scopePath = process.argv[2]

const matrix = JSON.parse(fs.readFileSync(matrixPath, "utf8"))
const scope = JSON.parse(fs.readFileSync(scopePath, "utf8"))

if (matrix.version !== "cicsc/postgres-exec-matrix-v1") {
  throw new Error(`unexpected postgres matrix version: ${matrix.version}`)
}
if (scope.version !== "cicsc/backend-scope-v1") {
  throw new Error(`unexpected postgres scope version: ${scope.version}`)
}
if (!Array.isArray(matrix.cases) || matrix.cases.length === 0) {
  throw new Error("postgres matrix must include at least one case")
}

const covered = new Set()
for (const c of matrix.cases) {
  if (!Array.isArray(c.operators) || c.operators.length === 0) {
    throw new Error(`matrix case ${c.id ?? "unknown"} has no operators`)
  }
  for (const op of c.operators) covered.add(op)
}

const missing = (scope.query?.supported ?? []).filter((op) => !covered.has(op))
if (missing.length) {
  throw new Error(`postgres matrix missing supported query operators: ${missing.join(", ")}`)
}

console.log(`postgres matrix check passed (${matrix.cases.length} cases, ${covered.size} operators).`)
NODE
