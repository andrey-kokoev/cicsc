#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MATRIX_PATH="${ROOT_DIR}/tests/conformance/required-matrix.json"

if [[ ! -f "${MATRIX_PATH}" ]]; then
  echo "missing conformance matrix: ${MATRIX_PATH}" >&2
  exit 1
fi

node - "${MATRIX_PATH}" "${ROOT_DIR}" <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const matrixPath = process.argv[2]
const rootDir = process.argv[3]
const json = JSON.parse(fs.readFileSync(matrixPath, "utf-8"))

if (json.version !== "cicsc/conformance-matrix-v1") {
  throw new Error(`unexpected conformance matrix version: ${json.version}`)
}

if (!Array.isArray(json.suites) || json.suites.length === 0) {
  throw new Error("conformance matrix must contain at least one suite")
}

const ids = new Set()
for (const s of json.suites) {
  if (!s.id || typeof s.id !== "string") {
    throw new Error("suite id must be a non-empty string")
  }
  if (ids.has(s.id)) {
    throw new Error(`duplicate suite id: ${s.id}`)
  }
  ids.add(s.id)

  if (!Array.isArray(s.test_files) || s.test_files.length === 0) {
    throw new Error(`suite ${s.id} must declare test_files`)
  }

  for (const rel of s.test_files) {
    const abs = path.join(rootDir, rel)
    if (!fs.existsSync(abs)) {
      throw new Error(`suite ${s.id} references missing test file: ${rel}`)
    }
  }
}

console.log(`conformance matrix check passed (${json.suites.length} suites).`)
NODE
