#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OBL_PATH="${1:-${ROOT_DIR}/docs/pilot/category-model-obligations.json}"
OUT_PATH="${2:-${ROOT_DIR}/docs/pilot/category-model-conformance.json}"
META_OUT_PATH="${CATEGORY_MODEL_CONFORMANCE_META_OUT:-}"
cd "${ROOT_DIR}"

node - "${OBL_PATH}" "${OUT_PATH}" "${META_OUT_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const oblPath = process.argv[2]
const outPath = process.argv[3]
const metaOutPath = process.argv[4] || ''
const model = JSON.parse(fs.readFileSync(path.resolve(oblPath), 'utf8'))

function getField(obj, fieldPath) {
  const parts = fieldPath.split('.')
  let cur = obj
  for (const p of parts) {
    if (cur == null || !(p in cur)) return undefined
    cur = cur[p]
  }
  return cur
}

function deepEqual(a, b) {
  return JSON.stringify(a) === JSON.stringify(b)
}

const results = []
let failCount = 0

for (const obl of model.obligations ?? []) {
  const checkResults = []
  for (const c of obl.checks ?? []) {
    let ok = false
    let detail = ''
    try {
      if (c.type === 'file') {
        ok = fs.existsSync(path.resolve(c.path))
        detail = ok ? 'exists' : 'missing'
      } else if (c.type === 'grep') {
        const p = path.resolve(c.path)
        if (!fs.existsSync(p)) {
          ok = false
          detail = 'file-missing'
        } else {
          const txt = fs.readFileSync(p, 'utf8')
          ok = new RegExp(c.pattern, 'm').test(txt)
          detail = ok ? 'matched' : 'pattern-not-found'
        }
      } else if (c.type === 'json_field') {
        const p = path.resolve(c.path)
        if (!fs.existsSync(p)) {
          ok = false
          detail = 'file-missing'
        } else {
          const j = JSON.parse(fs.readFileSync(p, 'utf8'))
          const got = getField(j, c.field)
          ok = deepEqual(got, c.equals)
          detail = ok ? 'field-match' : `field-mismatch` 
        }
      } else {
        ok = false
        detail = `unknown-check-type:${c.type}`
      }
    } catch (e) {
      ok = false
      detail = `error:${String(e.message || e)}`
    }

    if (!ok) failCount += 1
    checkResults.push({ ...c, ok, detail })
  }

  const pass = checkResults.every((x) => x.ok)
  results.push({ id: obl.id, section: obl.section, pass, checks: checkResults })
}

const report = {
  version: 'cicsc/category-model-conformance-v1',
  obligations_version: model.version,
  source_model_doc: model.model_doc,
  status: failCount === 0 ? 'pass' : 'fail',
  deterministic_report: true,
  obligations: results,
}

fs.writeFileSync(path.resolve(outPath), `${JSON.stringify(report, null, 2)}\n`, 'utf8')
if (metaOutPath) {
  const meta = {
    version: 'cicsc/category-model-conformance-meta-v1',
    generated_at_unix: Math.floor(Date.now() / 1000),
    source_report: path.relative(process.cwd(), path.resolve(outPath)),
    source_obligations: path.relative(process.cwd(), path.resolve(oblPath)),
  }
  fs.writeFileSync(path.resolve(metaOutPath), `${JSON.stringify(meta, null, 2)}\n`, 'utf8')
}
if (failCount === 0) {
  console.log(`category-model conformance check passed: ${outPath}`)
  process.exit(0)
}
console.error(`category-model conformance check failed: ${outPath}`)
for (const o of results) {
  if (o.pass) continue
  console.error(`- ${o.id}`)
  for (const c of o.checks) {
    if (!c.ok) console.error(`  * ${c.type} ${c.path || ''} ${c.field || c.pattern || ''}: ${c.detail}`)
  }
}
process.exit(1)
NODE
