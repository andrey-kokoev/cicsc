#!/usr/bin/env node
import { readFile, writeFile } from "node:fs/promises"
import { existsSync } from "node:fs"
import { dirname, resolve } from "node:path"
import { fileURLToPath } from "node:url"
import { spawnSync } from "node:child_process"

const __dirname = dirname(fileURLToPath(import.meta.url))
const MIGRATION_COMMANDS = new Set(["migration-preflight", "migration-dry-run", "migration-rollback"])
const LLM_PROVIDERS = new Set(["openai", "ollama", "anthropic", "openrouter", "kimi", "qwen", "azure-openai", "gemini", "local"])

const DEFAULT_LLM_PROVIDER = "gemini"

async function main () {
  const argv = process.argv.slice(2)
  const cmd = argv[0]
  const args = parseArgs(argv.slice(1))
  const server = String(args.server ?? "http://localhost")
  const token = typeof args.token === "string" ? args.token : null
  const llmProvider = String(args["llm-provider"] ?? DEFAULT_LLM_PROVIDER)
  const autoInstall = args["auto-install"] === true || args["auto-install"] === "true"

  if (args.help || args.h || cmd === "--help" || cmd === "-h") {
    printUsage()
    process.exit(0)
  }

  if (!cmd) {
    printUsage()
    process.exit(0)
  }

  if (cmd && MIGRATION_COMMANDS.has(cmd)) {
    maybeRerunWithTsLoader()
  }

  try {
    if (cmd === "init") {
      const interactive = args.interactive === true || args.interactive === "true"
      if (interactive) {
        await runInteractiveMode(llmProvider, args)
      } else {
        printInitUsage()
      }
      process.exit(0)
    }

    if (cmd === "compile") {
      const specPath = String(args.spec ?? "")
      if (!specPath) throw new Error("--spec is required")
      const spec = await readSpecFile(specPath)
      const body = await postJson(`${server}/compile`, spec, token)
      console.log(JSON.stringify(body, null, 2))
      
      if (autoInstall && body.ok) {
        console.log("\n--- Auto-installing after successful compile ---")
        const tenant_id = String(args.tenant ?? "t")
        const installBody = await postJson(`${server}/install-from-spec`, { ...spec, tenant_id }, token)
        console.log(JSON.stringify(installBody, null, 2))
        process.exit(installBody.ok ? 0 : 1)
      }
      
      process.exit(body.ok ? 0 : 1)
    }

    if (cmd === "generate-ui") {
      const specPath = String(args.spec ?? "")
      if (!specPath) throw new Error("--spec is required")
      const outputPath = String(args.out ?? "./ui-output")
      const spec = await readSpecFile(specPath)
      const { compileSpecToBundleV0 } = await import("../runtime/http/compile.ts")
      const { generateUiFromIr, generateVueComponents } = await import("../ui/generator.ts")
      
      const bundle = compileSpecToBundleV0(spec)
      const ui = generateUiFromIr(bundle.core_ir)
      const components = generateVueComponents(ui)
      
      const { mkdir, writeFile } = await import("node:fs/promises")
      await mkdir(outputPath, { recursive: true })
      
      await writeFile(`${outputPath}/ui-spec.json`, JSON.stringify(ui, null, 2), "utf8")
      
      for (const [filename, content] of Object.entries(components)) {
        await writeFile(`${outputPath}/${filename}`, content, "utf8")
      }
      
      console.log(`Generated UI spec: ${outputPath}/ui-spec.json`)
      console.log(`Generated ${Object.keys(components).length} Vue components in ${outputPath}/`)
      process.exit(0)
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

    if (cmd === "gates") {
      const suite = String(args.suite ?? "required")
      runGateSuite(suite)
      process.exit(0)
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
  node cli/cicsc.mjs init --interactive [--llm-provider <provider>] [--tenant <tenant_id>] [--auto-install]
  node cli/cicsc.mjs compile --spec <path> [--server <url>] [--token <auth-token>] [--llm-provider <provider>] [--auto-install] [--tenant <tenant_id>]
  node cli/cicsc.mjs generate-ui --spec <path> [--out <output-dir>]
  node cli/cicsc.mjs install --spec <path> --tenant <tenant_id> [--server <url>] [--token <auth-token>]
  node cli/cicsc.mjs verify --tenant <tenant_id> [--type <entity_type> --entity <entity_id>] [--server <url>] [--token <auth-token>]
  node cli/cicsc.mjs gates [--suite <required|cross-backend>]
  node cli/cicsc.mjs migration-preflight --from <bundle.json> --to <bundle.json> --events <events.json> --migration <id> [--actor <id> --now <ts>]
  node cli/cicsc.mjs migration-dry-run --from <bundle.json> --to <bundle.json> --events <events.json> --migration <id> [--artifact <report.json> --actor <id> --now <ts>]
  node cli/cicsc.mjs migration-rollback --to <bundle.json> --events <events.json> --migration <id> [--out-events <events.json>]

LLM Providers:
  openai, ollama, anthropic, openrouter, kimi, qwen, azure-openai, gemini, local
  Default: gemini

Examples:
  node cli/cicsc.mjs init --interactive
  node cli/cicsc.mjs init --interactive --llm-provider openai
  node cli/cicsc.mjs compile --spec spec.json --auto-install --tenant mytenant
  node cli/cicsc.mjs generate-ui --spec spec.json --out ./ui-output
`)
}

function printInitUsage () {
  console.log(`cicsc init

Usage:
  node cli/cicsc.mjs init --interactive [--llm-provider <provider>] [--tenant <tenant_id>] [--auto-install]

Options:
  --interactive     Start interactive interview mode to create a spec
  --llm-provider   LLM provider to use (default: gemini)
  --tenant         Tenant ID for auto-install (default: t)
  --auto-install   Automatically install after compile
`)
}

async function runInteractiveMode (llmProvider, args) {
  console.log("\n=== CICSC Interactive Mode ===\n")
  console.log(`Using LLM provider: ${llmProvider}`)
  console.log("Type 'exit' to quit at any time.\n")

  const { createLLMProvider, LLMInterviewEngine } = await import("../core/assistant/llm-adapter.ts")

  const apiKey = getApiKeyForProvider(llmProvider)
  const provider = createLLMProvider({
    provider: llmProvider,
    apiKey
  })

  const engine = new LLMInterviewEngine(provider)

  const rl = await import("readline")
  const readlineInterface = rl.createInterface({
    input: process.stdin,
    output: process.stdout
  })

  const question = (prompt) => new Promise((resolve) => {
    readlineInterface.question(prompt, resolve)
  })

  console.log(await engine.process(""))

  while (true) {
    const input = await question("\n> ")
    
    if (!input || input.toLowerCase() === "exit" || input.toLowerCase() === "quit") {
      console.log("\nGoodbye!")
      readlineInterface.close()
      break
    }

    if (input.toLowerCase() === "/spec") {
      console.log("\n" + engine.getSummary())
      continue
    }

    const response = await engine.process(input)
    console.log("\n" + response)

    const state = engine.getState()
    if (state.currentStep === "CONFIRM" && input.toLowerCase().includes("yes")) {
      const structured = engine.getStructuredSpec()
      const spec = structured.spec
      const specPath = args["spec-path"] ? String(args["spec-path"]) : "./spec-generated.json"
      await writeFile(specPath, JSON.stringify(spec, null, 2), "utf8")
      console.log(`\nSpec saved to: ${specPath}`)

      const preflightPath = args["preflight-path"] ? String(args["preflight-path"]) : "./spec-preflight.json"
      await writeFile(preflightPath, JSON.stringify({
        deployable: structured.deployable,
        blocking_issues: structured.blocking_issues,
      }, null, 2), "utf8")
      console.log(`Preflight report saved to: ${preflightPath}`)

      const server = String(args.server ?? "http://localhost")
      const token = typeof args.token === "string" ? args.token : null

      console.log("\n--- Compiling spec ---")
      const body = await postJson(`${server}/compile`, spec, token)
      console.log(JSON.stringify(body, null, 2))

      const autoInstall = args["auto-install"] === true || args["auto-install"] === "true"
      if (autoInstall && body.ok) {
        console.log("\n--- Auto-installing ---")
        const tenant_id = String(args.tenant ?? "t")
        const installBody = await postJson(`${server}/install-from-spec`, { ...spec, tenant_id }, token)
        console.log(JSON.stringify(installBody, null, 2))
      }

      readlineInterface.close()
      break
    }
  }
}

function getApiKeyForProvider (provider) {
  const envKeys = {
    openai: "OPENAI_API_KEY",
    anthropic: "ANTHROPIC_API_KEY",
    openrouter: "OPENROUTER_API_KEY",
    kimi: "KIMI_API_KEY",
    qwen: "DASHSCOPE_API_KEY",
    azureopenai: "AZURE_OPENAI_API_KEY",
    gemini: "GEMINI_API_KEY",
    local: "LOCAL_API_KEY"
  }
  const key = envKeys[provider.toLowerCase()]
  return key ? (typeof process !== "undefined" ? process.env[key] : "") || "" : ""
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

function runGateSuite (suite) {
  const suiteMap = {
    required: ["./scripts/run_conformance_required.sh", "default"],
    "cross-backend": ["./scripts/run_cross_backend_gate.sh"],
  }
  const cmd = suiteMap[suite]
  if (!cmd) {
    throw new Error(`unknown gate suite: ${suite}`)
  }
  const run = spawnSync(cmd[0], cmd.slice(1), {
    cwd: resolve(__dirname, ".."),
    stdio: "inherit",
    shell: false,
  })
  if (run.status !== 0) {
    process.exit(run.status ?? 1)
  }
}

void main()
