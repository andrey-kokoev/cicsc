#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase11-gate.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const outPath = process.argv[2]
const checklistPath = "docs/pilot/phase10-exit-checklist.json"
const checklist = JSON.parse(fs.readFileSync(path.resolve(checklistPath), "utf8"))
const allPass = (checklist.items ?? []).every((i) => i.status === "pass")
const blocked = !allPass
const reasons = blocked
  ? (checklist.items ?? []).filter((i) => i.status !== "pass").map((i) => i.id)
  : []

const report = {
  version: "cicsc/phase11-gate-v1",
  timestamp_unix: Math.floor(Date.now() / 1000),
  blocked,
  basis: checklistPath,
  reasons,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, "utf8")
console.log(`phase11 gate report written: ${outPath}`)
process.exit(blocked ? 1 : 0)
NODE
