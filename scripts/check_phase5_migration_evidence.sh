#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const p = path.resolve("docs/pilot/phase5-migration-drill-evidence.json")
const j = JSON.parse(fs.readFileSync(p, "utf8"))

if (j.version !== "cicsc/phase5-migration-drill-evidence-v1") {
  throw new Error(`unexpected migration evidence version: ${j.version}`)
}
if (!j.runbook || !fs.existsSync(path.resolve(j.runbook))) {
  throw new Error(`missing runbook: ${j.runbook}`)
}
for (const a of j.drill_artifacts ?? []) {
  if (!fs.existsSync(path.resolve(a))) throw new Error(`missing drill artifact: ${a}`)
}
if (j.status !== "pass") {
  throw new Error(`migration drill evidence not passing: ${j.status}`)
}
console.log("phase5 migration evidence check passed")
NODE
