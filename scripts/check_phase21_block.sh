#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase21-gate.json}"
cd "${ROOT_DIR}"
node - "${OUT_PATH}" <<'NODE'
const fs=require('node:fs');const path=require('node:path')
const outPath=process.argv[2]
const checklist=JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase20-exit-checklist.json'),'utf8'))
const roadmap=fs.readFileSync(path.resolve('ROADMAP.md'),'utf8')
const checklistPass=(checklist.items??[]).every(i=>i.status==='pass')
const ak=[...roadmap.matchAll(/^- \[(x| )\] AK(\d)\.(\d)\s+/gm)]
const allAk=ak.length>0&&ak.every(m=>m[1]==='x')
const blocked=!(checklistPass&&allAk)
const reasons=[]
if(!checklistPass) reasons.push('phase20_exit_checklist_not_pass')
if(!allAk) reasons.push('roadmap_ak_series_incomplete')
const report={version:'cicsc/phase21-gate-v1',timestamp_unix:Math.floor(Date.now()/1000),blocked,basis:{checklist:'docs/pilot/phase20-exit-checklist.json',roadmap:'ROADMAP.md'},reasons}
fs.writeFileSync(outPath,`${JSON.stringify(report,null,2)}\n`,'utf8')
process.exit(blocked?1:0)
NODE
