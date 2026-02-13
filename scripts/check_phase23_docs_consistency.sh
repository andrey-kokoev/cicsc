#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase23-doc-consistency.json}"
cd "${ROOT_DIR}"
node - "${OUT_PATH}" <<'NODE'
const fs=require('node:fs');const path=require('node:path')
const outPath=process.argv[2]
const phase=fs.readFileSync(path.resolve('PHASE23.md'),'utf8')
const roadmap=fs.readFileSync(path.resolve('ROADMAP.md'),'utf8')
const parse=(md,re,prefix)=>{const out=new Map();let m;while((m=re.exec(md))!==null)out.set(`${prefix}${m[2]}.${m[3]}`,m[1]==='x');return out}
const phaseMap=parse(phase,/^- \[(x| )\] P23\.(\d)\.(\d)\s+/gm,'AN')
const roadmapMap=parse(roadmap,/^- \[(x| )\] AN(\d)\.(\d)\s+/gm,'AN')
const mismatches=[]
for(const [id,checked] of phaseMap.entries()){if(!roadmapMap.has(id))mismatches.push({id,reason:'missing_in_roadmap'});else if(roadmapMap.get(id)!==checked)mismatches.push({id,reason:'status_mismatch'})}
for(const [id] of roadmapMap.entries()){if(!phaseMap.has(id))mismatches.push({id,reason:'missing_in_phase23'})}
const report={version:'cicsc/phase23-doc-consistency-v1',timestamp_unix:Math.floor(Date.now()/1000),status:mismatches.length===0?'pass':'fail',mismatches}
fs.writeFileSync(outPath,`${JSON.stringify(report,null,2)}\n`,'utf8')
process.exit(mismatches.length===0?0:1)
NODE
