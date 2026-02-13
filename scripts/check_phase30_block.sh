#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase30-gate.json}"
cd "${ROOT_DIR}"
node - "${OUT_PATH}" <<'NODE'
const fs=require('node:fs');const path=require('node:path')
const outPath=process.argv[2]
const checklist=JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase29-exit-checklist.json'),'utf8'))
const roadmap=fs.readFileSync(path.resolve('ROADMAP.md'),'utf8')
const checklistPass=(checklist.items??[]).every(i=>i.status==='pass')
const at=[...roadmap.matchAll(/^- \[(x| )\] AT(\d)\.(\d)\s+/gm)]
const allAt=at.length>0&&at.every(m=>m[1]==='x')
const blocked=!(checklistPass&&allAt)
const reasons=[]
if(!checklistPass) reasons.push('phase29_exit_checklist_not_pass')
if(!allAt) reasons.push('roadmap_at_series_incomplete')
const report={version:'cicsc/phase30-gate-v1',timestamp_unix:Math.floor(Date.now()/1000),blocked,basis:{checklist:'docs/pilot/phase29-exit-checklist.json',roadmap:'ROADMAP.md'},reasons}
fs.writeFileSync(outPath,`${JSON.stringify(report,null,2)}\n`,'utf8')
process.exit(blocked?1:0)
NODE
