#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require('node:fs')
const path = require('node:path')
const { spawnSync } = require('node:child_process')

const roadmap = fs.readFileSync(path.resolve('ROADMAP.md'), 'utf8').split(/\r?\n/)
const phaseSectionRe = /^## ([A-Z]{1,2})\. Phase (\d+):\s+/
const checkboxRe = /^- \[(x| )\] ([A-Z]{1,2}\d\.\d)\s+/

let phaseNo = null
const errors = []
for (const line of roadmap) {
  const p = line.match(phaseSectionRe)
  if (p) {
    phaseNo = Number(p[2])
    continue
  }
  const c = line.match(checkboxRe)
  if (!c || phaseNo === null) continue
  if (c[1] !== 'x') continue

  const checkboxId = c[2].toLowerCase()
  const token = `phase${phaseNo} ${checkboxId}`
  const run = spawnSync('git', ['log', '--all', '--regexp-ignore-case', '--grep', token, '--oneline', '-n', '1'], {
    cwd: process.cwd(),
    encoding: 'utf8',
  })
  if ((run.stdout ?? '').trim().length === 0) {
    errors.push(`missing commit evidence for checked checkbox ${c[2]} (expected token: \"${token}\")`)
  }
}

if (errors.length > 0) {
  console.error('checkbox commit evidence check failed')
  for (const e of errors) console.error(`- ${e}`)
  process.exit(1)
}

console.log('checkbox commit evidence check passed')
NODE
