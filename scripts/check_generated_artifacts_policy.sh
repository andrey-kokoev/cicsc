#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node <<'NODE'
const fs = require('node:fs')
const path = require('node:path')
const { execSync } = require('node:child_process')

const errors = []
let files = []
try {
  const out = execSync("rg --files -g '*.generated.*'", { encoding: 'utf8' }).trim()
  files = out ? out.split(/\r?\n/) : []
} catch {
  files = []
}

const textExts = new Set(['.md', '.txt', '.yaml', '.yml', '.sh', '.mmd'])

for (const rel of files) {
  const ext = path.extname(rel)
  const abs = path.resolve(rel)

  if (!fs.existsSync(abs)) {
    errors.push(`${rel}: missing file`)
    continue
  }

  if (ext === '.json') {
    try {
      const obj = JSON.parse(fs.readFileSync(abs, 'utf8'))
      if (obj._generated !== true) errors.push(`${rel}: missing _generated=true`)
      if (typeof obj._source !== 'string' || !obj._source) errors.push(`${rel}: missing _source`)
      if (typeof obj._generator !== 'string' || !obj._generator) errors.push(`${rel}: missing _generator`)
    } catch {
      errors.push(`${rel}: invalid JSON`)
    }
    continue
  }

  if (textExts.has(ext)) {
    const head = fs.readFileSync(abs, 'utf8').split(/\r?\n/).slice(0, 8).join('\n')
    if (!head.includes('AUTO-GENERATED FILE. DO NOT EDIT.')) {
      errors.push(`${rel}: missing auto-generated banner`)
    }
    if (!head.includes('Source:')) {
      errors.push(`${rel}: missing Source marker`)
    }
    if (!head.includes('Generator:')) {
      errors.push(`${rel}: missing Generator marker`)
    }
  }
}

if (errors.length) {
  console.error('generated artifacts policy check failed')
  for (const e of errors) console.error(`- ${e}`)
  process.exit(1)
}

console.log('generated artifacts policy check passed')
NODE
