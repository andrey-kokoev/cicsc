#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const phase = fs.readFileSync(path.resolve("PHASE5.md"), "utf8")
const roadmap = fs.readFileSync(path.resolve("ROADMAP.md"), "utf8")
const exitChecklist = JSON.parse(fs.readFileSync(path.resolve("docs/pilot/phase5-exit-checklist.json"), "utf8"))

function parsePhaseStatuses(md) {
  const out = new Map()
  const re = /^- \[(x| )\] P5\.(\d)\.(\d)\s+/gm
  let m
  while ((m = re.exec(md)) !== null) {
    out.set(`U${m[2]}.${m[3]}`, m[1] === "x")
  }
  return out
}

function parseRoadmapStatuses(md) {
  const out = new Map()
  const re = /^- \[(x| )\] U(\d)\.(\d)\s+/gm
  let m
  while ((m = re.exec(md)) !== null) {
    out.set(`U${m[2]}.${m[3]}`, m[1] === "x")
  }
  return out
}

const phaseMap = parsePhaseStatuses(phase)
const roadmapMap = parseRoadmapStatuses(roadmap)

for (const [id, checked] of phaseMap.entries()) {
  if (!roadmapMap.has(id)) throw new Error(`missing ${id} in ROADMAP.md`)
  if (roadmapMap.get(id) !== checked) throw new Error(`status mismatch for ${id} between PHASE5.md and ROADMAP.md`)
}

for (const [id] of roadmapMap.entries()) {
  if (!phaseMap.has(id)) throw new Error(`missing ${id} in PHASE5.md`)
}

const hasUnchecked = [...roadmapMap.values()].some((v) => !v)
if (exitChecklist.phase6_ready === true && hasUnchecked) {
  throw new Error("phase6_ready=true is invalid while U-series checkboxes remain unchecked")
}

console.log("phase5 docs consistency check passed")
NODE
