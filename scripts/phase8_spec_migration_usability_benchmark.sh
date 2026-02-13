#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_JSON="${1:-${ROOT_DIR}/docs/pilot/phase8-spec-migration-usability-benchmark.json}"
OUT_MD="${2:-${ROOT_DIR}/docs/pilot/phase8-spec-migration-usability-benchmark.md}"

cd "${ROOT_DIR}"

node - "${OUT_JSON}" "${OUT_MD}" <<'NODE'
const fs = require("node:fs")
const path = require("node:path")

const outJson = process.argv[2]
const outMd = process.argv[3]

const verticals = [
  { id: "ticketing", spec: "verticals/ticketing/spec.v1.json", migration: "verticals/ticketing/migration.v0_to_v1.json" },
  { id: "crm", spec: "verticals/crm/spec.v1.json", migration: "verticals/crm/migration.v0_to_v1.json" },
  { id: "kanban", spec: "verticals/kanban/spec.v1.json", migration: "verticals/kanban/migration.v0_to_v1.json" },
]

function countCommands(entity) {
  return Object.keys(entity.commands ?? {}).length
}

function countReducers(entity) {
  return Object.keys(entity.reducers ?? {}).length
}

function readJson(p) {
  return JSON.parse(fs.readFileSync(path.resolve(p), "utf8"))
}

const rows = verticals.map((v) => {
  const spec = readJson(v.spec)
  const migrationDoc = readJson(v.migration)
  const entities = Object.values(spec.entities ?? {})
  const entityCount = entities.length
  const stateCount = entities.reduce((n, e) => n + (Array.isArray(e.states) ? e.states.length : 0), 0)
  const commandCount = entities.reduce((n, e) => n + countCommands(e), 0)
  const reducerCount = entities.reduce((n, e) => n + countReducers(e), 0)

  const migrationEntries = Object.values(migrationDoc.migrations ?? {})
  const migrationCount = migrationEntries.length
  const transformCount = migrationEntries.reduce((n, m) => n + Object.keys(m.event_transforms ?? {}).length, 0)
  const stateMapCount = migrationEntries.reduce((n, m) => n + Object.keys(m.state_map ?? {}).length, 0)

  const status = entityCount > 0 && migrationCount > 0 && transformCount > 0 && stateMapCount > 0
    ? "pass"
    : "fail"

  return {
    vertical: v.id,
    spec_path: v.spec,
    migration_path: v.migration,
    entity_count: entityCount,
    state_count: stateCount,
    command_count: commandCount,
    reducer_count: reducerCount,
    migration_count: migrationCount,
    transform_count: transformCount,
    state_map_count: stateMapCount,
    status,
  }
})

const report = {
  version: "cicsc/phase8-spec-migration-usability-benchmark-v1",
  timestamp_unix: Math.floor(Date.now() / 1000),
  benchmark_axis: [
    "spec_surface_size",
    "command_reducer_density",
    "migration_transform_density",
    "state_map_completeness"
  ],
  verticals: rows,
  summary: {
    total_verticals: rows.length,
    passing_verticals: rows.filter((r) => r.status === "pass").length,
    failing_verticals: rows.filter((r) => r.status !== "pass").map((r) => r.vertical),
  },
}

fs.writeFileSync(outJson, `${JSON.stringify(report, null, 2)}\n`, "utf8")

const lines = []
lines.push("# Phase 8 Spec/Migration Usability Benchmark")
lines.push("")
lines.push(`Artifact: \`${path.relative(process.cwd(), outJson)}\``)
lines.push("")
lines.push("| Vertical | Entities | States | Commands | Reducers | Transforms | State Map | Status |")
lines.push("| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |")
for (const r of rows) {
  lines.push(`| ${r.vertical} | ${r.entity_count} | ${r.state_count} | ${r.command_count} | ${r.reducer_count} | ${r.transform_count} | ${r.state_map_count} | ${r.status} |`)
}
lines.push("")
lines.push(`Passing verticals: ${report.summary.passing_verticals}/${report.summary.total_verticals}`)
if (report.summary.failing_verticals.length > 0) {
  lines.push(`Failing verticals: ${report.summary.failing_verticals.join(", ")}`)
}

fs.writeFileSync(outMd, `${lines.join("\n")}\n`, "utf8")
console.log(`phase8 usability benchmark written: ${outJson}`)
console.log(`phase8 usability benchmark summary: ${outMd}`)
NODE
