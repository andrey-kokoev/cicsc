#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./scripts/check_phase6_docs_consistency.sh
./scripts/check_phase6_required_gates.sh

node <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const required = [
  "docs/pilot/phase6-field-baseline-report.json",
  "docs/pilot/phase6-concurrency-contract.json",
  "docs/pilot/phase6-concurrency-conformance.json",
  "docs/pilot/phase6-migration-concurrency-drill.json",
  "docs/pilot/phase6-cli-contract.json",
  "docs/pilot/phase6-sdk-contract.json",
  "docs/pilot/phase6-policy-control-matrix.json",
  "docs/pilot/phase6-feature-gates.json",
  "docs/pilot/phase6-required-gates.json",
  "docs/pilot/phase6-multi-vertical-field-report.json",
  "docs/pilot/phase6-exit-checklist.json",
]

for (const rel of required) {
  const full = path.resolve(rel)
  if (!fs.existsSync(full)) {
    throw new Error(`missing required artifact: ${rel}`)
  }
  if (rel.endsWith(".json")) {
    JSON.parse(fs.readFileSync(full, "utf8"))
  }
}

console.log("phase6 artifact gates check passed")
NODE
