#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase19-baseline-continuity.json}"
cd "${ROOT_DIR}"
node - "${OUT_PATH}" <<'NODE'
const fs=require('node:fs');const path=require('node:path');
const outPath=process.argv[2]
const phase18Checklist=JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase18-exit-checklist.json'),'utf8'))
const phase19Gate=JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase19-gate.json'),'utf8'))
const proof=JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase18-expansion-proof-closure-report.json'),'utf8'))
const continuity=JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase18-production-continuity-closure-report.json'),'utf8'))
const checks={
 phase18_exit_checklist:{basis:'docs/pilot/phase18-exit-checklist.json',status:(phase18Checklist.items??[]).every(i=>i.status==='pass')?'pass':'fail'},
 phase19_gate_open:{basis:'docs/pilot/phase19-gate.json',status:phase19Gate.blocked===false?'pass':'fail'},
 expansion_proof_continuity:{basis:'docs/pilot/phase18-expansion-proof-closure-report.json',status:proof.status==='pass'?'pass':'fail'},
 production_continuity_continuity:{basis:'docs/pilot/phase18-production-continuity-closure-report.json',status:continuity.status==='pass'?'pass':'fail'},
}
const overall=Object.values(checks).every(c=>c.status==='pass')?'pass':'fail'
const report={version:'cicsc/phase19-baseline-continuity-v1',timestamp_unix:Math.floor(Date.now()/1000),overall,checks}
fs.writeFileSync(outPath,`${JSON.stringify(report,null,2)}\n`,'utf8')
console.log(`phase19 baseline continuity report written: ${outPath}`)
process.exit(overall==='pass'?0:1)
NODE
