#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase23-gate.json}"
cd "${ROOT_DIR}"
node - "${OUT_PATH}" <<'NODE'
const fs=require('node:fs');const path=require('node:path')
const outPath=process.argv[2]
const checklist=JSON.parse(fs.readFileSync(path.resolve('docs/pilot/phase22-exit-checklist.json'),'utf8'))
const roadmap=fs.readFileSync(path.resolve('ROADMAP.md'),'utf8')
const checklistPass=(checklist.items??[]).every(i=>i.status==='pass')
const am=[...roadmap.matchAll(/^- \[(x| )\] AM(\d)\.(\d)\s+/gm)]
const allAm=am.length>0&&am.every(m=>m[1]==='x')
const blocked=!(checklistPass&&allAm)
const reasons=[]
if(!checklistPass) reasons.push('phase22_exit_checklist_not_pass')
if(!allAm) reasons.push('roadmap_am_series_incomplete')
const report={version:'cicsc/phase23-gate-v1',timestamp_unix:Math.floor(Date.now()/1000),blocked,basis:{checklist:'docs/pilot/phase22-exit-checklist.json',roadmap:'ROADMAP.md'},reasons}
fs.writeFileSync(outPath,`${JSON.stringify(report,null,2)}\n`,'utf8')
process.exit(blocked?1:0)
NODE
