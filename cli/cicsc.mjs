#!/usr/bin/env node
import { readFile } from "node:fs/promises"
import { writeFile } from "node:fs/promises"
import { dirname, resolve } from "node:path"
import { fileURLToPath } from "node:url"
import { spawnSync } from "node:child_process"

const __dirname = dirname(fileURLToPath(import.meta.url))
const MIGRATION_COMMANDS = new Set(["migration-preflight", "migration-dry-run", "migration-rollback"])

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

  if (cmd && MIGRATION_COMMANDS.has(cmd)) {
    maybeRerunWithTsLoader()
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

    if (cmd === "migration-preflight") {
      const payload = await readMigrationPayload(args)
      const { preflightMigration } = await import("../core/runtime/migration-preflight.ts")
      const report = preflightMigration(payload)
      console.log(JSON.stringify(report, null, 2))
      process.exit(report.ok ? 0 : 1)
    }

    if (cmd === "migration-dry-run") {
      const payload = await readMigrationPayload(args)
      const artifactPath = typeof args.artifact === "string" ? args.artifact : null
      const { runMigrationDryRun } = await import("../core/runtime/migration-dry-run.ts")
      const report = await runMigrationDryRun({
        ...payload,
        write_artifact: artifactPath
          ? async (artifact) => {
              await writeFile(artifactPath, JSON.stringify(artifact, null, 2), "utf8")
            }
          : undefined,
      })
      console.log(JSON.stringify(report, null, 2))
      process.exit(report.ok ? 0 : 1)
    }

    if (cmd === "migration-rollback") {
      const payload = await readRollbackPayload(args)
      const outEventsPath = typeof args["out-events"] === "string" ? args["out-events"] : null
      const { rollbackMigrationChain } = await import("../core/runtime/rollback.ts")
      const report = rollbackMigrationChain({
        to_bundle: payload.to_bundle,
        migration_id: payload.migration_id,
        events: payload.events,
        intrinsics: payload.intrinsics,
      })
      if (outEventsPath && report.ok) {
        await writeFile(outEventsPath, JSON.stringify(report.events ?? [], null, 2), "utf8")
      }
      console.log(JSON.stringify(report, null, 2))
      process.exit(report.ok ? 0 : 1)
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

async function readJsonFile (path) {
  const text = await readFile(path, "utf8")
  return JSON.parse(text)
}

async function readMigrationPayload (args) {
  const fromPath = String(args.from ?? "")
  const toPath = String(args.to ?? "")
  const eventsPath = String(args.events ?? "")
  const migration_id = String(args.migration ?? "")
  if (!fromPath) throw new Error("--from is required")
  if (!toPath) throw new Error("--to is required")
  if (!eventsPath) throw new Error("--events is required")
  if (!migration_id) throw new Error("--migration is required")

  const from_bundle = await readJsonFile(fromPath)
  const to_bundle = await readJsonFile(toPath)
  const events = await readJsonFile(eventsPath)

  const intrinsics = {
    has_role: () => false,
    role_of: () => "user",
    auth_ok: () => true,
    constraint: () => true,
    len: (v) => (Array.isArray(v) || typeof v === "string" ? v.length : null),
    str: (v) => (v == null ? null : String(v)),
    int: (v) => (typeof v === "number" ? Math.trunc(v) : null),
    float: (v) => (typeof v === "number" ? v : null),
  }

  return {
    from_bundle,
    to_bundle,
    migration_id,
    events,
    now: Number(args.now ?? Date.now()),
    actor: String(args.actor ?? "cli"),
    intrinsics,
  }
}

async function readRollbackPayload (args) {
  const toPath = String(args.to ?? "")
  const eventsPath = String(args.events ?? "")
  const migration_id = String(args.migration ?? "")
  if (!toPath) throw new Error("--to is required")
  if (!eventsPath) throw new Error("--events is required")
  if (!migration_id) throw new Error("--migration is required")

  const to_bundle = await readJsonFile(toPath)
  const events = await readJsonFile(eventsPath)
  const intrinsics = {
    has_role: () => false,
    role_of: () => "user",
    auth_ok: () => true,
    constraint: () => true,
    len: (v) => (Array.isArray(v) || typeof v === "string" ? v.length : null),
    str: (v) => (v == null ? null : String(v)),
    int: (v) => (typeof v === "number" ? Math.trunc(v) : null),
    float: (v) => (typeof v === "number" ? v : null),
  }

  return {
    to_bundle,
    migration_id,
    events,
    intrinsics,
  }
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
  node cli/cicsc.mjs migration-preflight --from <bundle.json> --to <bundle.json> --events <events.json> --migration <id> [--actor <id> --now <ts>]
  node cli/cicsc.mjs migration-dry-run --from <bundle.json> --to <bundle.json> --events <events.json> --migration <id> [--artifact <report.json> --actor <id> --now <ts>]
  node cli/cicsc.mjs migration-rollback --to <bundle.json> --events <events.json> --migration <id> [--out-events <events.json>]
`)
}

function maybeRerunWithTsLoader () {
  const loaderFlagPresent = process.execArgv.some((arg) => arg.includes("ts-extension-loader.mjs"))
  if (loaderFlagPresent) return

  const loaderPath = resolve(__dirname, "../tests/harness/ts-extension-loader.mjs")
  const rerun = spawnSync(process.execPath, ["--loader", loaderPath, ...process.argv.slice(1)], {
    stdio: "inherit",
  })
  process.exit(rerun.status ?? 1)
}

void main()
