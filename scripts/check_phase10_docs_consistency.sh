#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase10-doc-consistency.json}"
cd "${ROOT_DIR}"

node - "${OUT_PATH}" <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const outPath = process.argv[2]
const phase = fs.readFileSync(path.resolve("PHASE10.md"), "utf8")
const roadmap = fs.readFileSync(path.resolve("ROADMAP.md"), "utf8")
const exitChecklist = JSON.parse(fs.readFileSync(path.resolve("docs/pilot/phase10-exit-checklist.json"), "utf8"))

function parsePhaseStatuses(md) {
  const out = new Map()
  const re = /^- \[(x| )\] P10\.(\d)\.(\d)\s+/gm
  let m
  while ((m = re.exec(md)) !== null) {
    out.set(`AA${m[2]}.${m[3]}`, m[1] === "x")
  }
  return out
}

function parseRoadmapStatuses(md) {
  const out = new Map()
  const re = /^- \[(x| )\] AA(\d)\.(\d)\s+/gm
  let m
  while ((m = re.exec(md)) !== null) {
    out.set(`AA${m[2]}.${m[3]}`, m[1] === "x")
  }
  return out
}

const phaseMap = parsePhaseStatuses(phase)
const roadmapMap = parseRoadmapStatuses(roadmap)
const mismatches = []

for (const [id, checked] of phaseMap.entries()) {
  if (!roadmapMap.has(id)) {
    mismatches.push({ id, reason: "missing_in_roadmap" })
    continue
  }
  if (roadmapMap.get(id) !== checked) {
    mismatches.push({ id, reason: "status_mismatch" })
  }
}

for (const [id] of roadmapMap.entries()) {
  if (!phaseMap.has(id)) {
    mismatches.push({ id, reason: "missing_in_phase10" })
  }
}

const hasUnchecked = [...roadmapMap.values()].some((v) => !v)
const governance = exitChecklist.items?.find((i) => i.id === "P10_EXIT_GOVERNANCE_DRIFT")
const governanceMismatch = governance?.status === "pass" && hasUnchecked
if (governanceMismatch) {
  mismatches.push({
    id: "P10_EXIT_GOVERNANCE_DRIFT",
    reason: "invalid_pass_while_aa_series_unchecked",
  })
}

const report = {
  version: "cicsc/phase10-doc-consistency-v1",
  timestamp_unix: Math.floor(Date.now() / 1000),
  status: mismatches.length === 0 ? "pass" : "fail",
  basis: {
    phase10: "PHASE10.md",
    roadmap: "ROADMAP.md",
    checklist: "docs/pilot/phase10-exit-checklist.json",
  },
  checked_ids: [...roadmapMap.keys()].sort(),
  has_unchecked: hasUnchecked,
  mismatches,
}

fs.writeFileSync(outPath, `${JSON.stringify(report, null, 2)}\n`, "utf8")
if (mismatches.length === 0) {
  console.log("phase10 docs consistency check passed")
  process.exit(0)
}
console.error("phase10 docs consistency check failed")
for (const m of mismatches) {
  console.error(`- ${m.id}: ${m.reason}`)
}
process.exit(1)
NODE
