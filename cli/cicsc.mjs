#!/usr/bin/env node
import { readFile } from "node:fs/promises"

async function main () {
  const argv = process.argv.slice(2)
  const cmd = argv[0]
  const args = parseArgs(argv.slice(1))
  const server = String(args.server ?? "http://localhost")
  const token = typeof args.token === "string" ? args.token : null

  if (!cmd || args.help || args.h) {
    printUsage()
    process.exit(0)
  }

  try {
    if (cmd === "compile") {
      const specPath = String(args.spec ?? "")
      if (!specPath) throw new Error("--spec is required")
      const spec = await readSpecFile(specPath)
      const body = await postJson(`${server}/compile`, spec, token)
      console.log(JSON.stringify(body, null, 2))
      process.exit(body.ok ? 0 : 1)
    }

    if (cmd === "install") {
      const specPath = String(args.spec ?? "")
      if (!specPath) throw new Error("--spec is required")
      const tenant_id = String(args.tenant ?? "t")
      const spec = await readSpecFile(specPath)
      const body = await postJson(`${server}/install-from-spec`, { ...spec, tenant_id }, token)
      console.log(JSON.stringify(body, null, 2))
      process.exit(body.ok ? 0 : 1)
    }

    if (cmd === "verify") {
      const tenant_id = String(args.tenant ?? "")
      if (!tenant_id) throw new Error("--tenant is required")
      const payload = {
        tenant_id,
        ...(args.type ? { entity_type: String(args.type) } : {}),
        ...(args.entity ? { entity_id: String(args.entity) } : {}),
      }
      const body = await postJson(`${server}/verify`, payload, token)
      console.log(JSON.stringify(body, null, 2))
      process.exit(body.ok ? 0 : 1)
    }

    throw new Error(`unknown command: ${cmd}`)
  } catch (e) {
    console.error((e && e.message) || String(e))
    process.exit(1)
  }
}

function parseArgs (argv) {
  const out = {}
  for (let i = 0; i < argv.length; i++) {
    const tok = argv[i]
    if (!tok.startsWith("--")) continue
    const key = tok.slice(2)
    const nxt = argv[i + 1]
    if (!nxt || nxt.startsWith("--")) out[key] = true
    else {
      out[key] = nxt
      i++
    }
  }
  return out
}

async function readSpecFile (path) {
  const text = await readFile(path, "utf8")
  return JSON.parse(text)
}

async function postJson (url, payload, token) {
  const headers = { "content-type": "application/json" }
  if (token) headers.authorization = `Bearer ${token}`

  const res = await fetch(url, {
    method: "POST",
    headers,
    body: JSON.stringify(payload),
  })

  const body = await res.json().catch(() => ({}))
  if (!res.ok) {
    const msg = body && body.error ? String(body.error) : `HTTP ${res.status}`
    throw new Error(msg)
  }
  return body
}

function printUsage () {
  console.log(`cicsc CLI

Usage:
  node cli/cicsc.mjs compile --spec <path> [--server <url>] [--token <auth-token>]
  node cli/cicsc.mjs install --spec <path> --tenant <tenant_id> [--server <url>] [--token <auth-token>]
  node cli/cicsc.mjs verify --tenant <tenant_id> [--type <entity_type> --entity <entity_id>] [--server <url>] [--token <auth-token>]
`)
}

void main()
