#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./scripts/check_phase7_docs_consistency.sh
./scripts/check_phase7_required_gates.sh

node <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const required = [
  "docs/pilot/phase7-parity-scope-matrix.json",
  "docs/pilot/phase7-parity-differential.json",
  "docs/pilot/phase7-failfast-scope.json",
  "docs/pilot/phase7-backend-parity-report.json",
  "docs/pilot/phase7-parity-deltas.json",
  "docs/pilot/phase7-concurrency-contract-delta.json",
  "docs/pilot/phase7-concurrency-adversarial.json",
  "docs/pilot/phase7-isolation-differential.json",
  "docs/pilot/phase7-conflict-matrix-expanded.json",
  "docs/pilot/phase7-migration-protocol-contract.json",
  "docs/pilot/phase7-tenant-batch-migration-drill.json",
  "docs/pilot/phase7-post-cutover-differential.json",
  "docs/pilot/phase7-migration-safety-report.json",
  "docs/pilot/phase7-required-gates.json",
  "docs/pilot/phase7-unresolved-criticals-register.json",
  "docs/pilot/phase7-exit-checklist.json",
]

for (const rel of required) {
  const full = path.resolve(rel)
  if (!fs.existsSync(full)) throw new Error(`missing required artifact: ${rel}`)
  JSON.parse(fs.readFileSync(full, "utf8"))
}

console.log("phase7 artifact gates check passed")
NODE
