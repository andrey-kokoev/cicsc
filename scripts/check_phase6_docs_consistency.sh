#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const phase = fs.readFileSync(path.resolve("PHASE6.md"), "utf8")
const roadmap = fs.readFileSync(path.resolve("ROADMAP.md"), "utf8")
const exitChecklist = JSON.parse(fs.readFileSync(path.resolve("docs/pilot/phase6-exit-checklist.json"), "utf8"))

function parsePhaseStatuses(md) {
  const out = new Map()
  const re = /^- \[(x| )\] P6\.(\d)\.(\d)\s+/gm
  let m
  while ((m = re.exec(md)) !== null) {
    out.set(`W${m[2]}.${m[3]}`, m[1] === "x")
  }
  return out
}

function parseRoadmapStatuses(md) {
  const out = new Map()
  const re = /^- \[(x| )\] W(\d)\.(\d)\s+/gm
  let m
  while ((m = re.exec(md)) !== null) {
    out.set(`W${m[2]}.${m[3]}`, m[1] === "x")
  }
  return out
}

const phaseMap = parsePhaseStatuses(phase)
const roadmapMap = parseRoadmapStatuses(roadmap)

for (const [id, checked] of phaseMap.entries()) {
  if (!roadmapMap.has(id)) throw new Error(`missing ${id} in ROADMAP.md`)
  if (roadmapMap.get(id) !== checked) throw new Error(`status mismatch for ${id} between PHASE6.md and ROADMAP.md`)
}

for (const [id] of roadmapMap.entries()) {
  if (!phaseMap.has(id)) throw new Error(`missing ${id} in PHASE6.md`)
}

const hasUnchecked = [...roadmapMap.values()].some((v) => !v)
const phase7Gate = exitChecklist.items?.find((i) => i.id === "P6_EXIT_GOVERNANCE_CI")
if (phase7Gate?.status === "pass" && hasUnchecked) {
  throw new Error("P6_EXIT_GOVERNANCE_CI=pass is invalid while W-series checkboxes remain unchecked")
}

console.log("phase6 docs consistency check passed")
NODE
