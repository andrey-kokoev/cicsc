// /tests/conformance/random-oracle-harness.ts
// Phase 4: Deterministic seed replay artifact support (P4.2.3)

import assert from "node:assert/strict"
import * as fs from "node:fs"
import * as path from "node:path"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { installSqliteSchemaV0, openSqliteMemory, runLoweredQueryPlan, upsertSnapshot } from "../harness/sqlite-memory"
import { type ReplayArtifact, toReplayArtifact, regenerateFromArtifact } from "./random-query-generator"

function stableNormalize (v: any): any {
  if (v === null || typeof v !== "object") return v
  if (Array.isArray(v)) return v.map(stableNormalize)
  const out: any = {}
  for (const k of Object.keys(v).sort()) out[k] = stableNormalize(v[k])
  return out
}

function canonRows (rows: any[]): any[] {
  const norm = rows.map(stableNormalize)
  norm.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)))
  return norm
}

function oracleCtx (snapRows: any[]) {
  return {
    now: 1,
    actor: "u",
    snap: () => snapRows,
    sla_status: () => [],
    baseEnv: {
      now: 1,
      actor: "u",
      state: "",
      input: {},
      attrs: {},
      arg: {},
      intrinsics: {
        has_role: () => false,
        role_of: () => "agent",
        auth_ok: () => true,
        constraint: () => true,
        len: () => 0,
        str: (v: any) => (v === null ? null : String(v)),
        int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
        float: (v: any) => (typeof v === "number" ? v : null),
      },
    },
  }
}

/** Configuration for failure artifact capture */
export type HarnessConfig = {
  /** Directory to write replay artifacts on failure (P4.2.3) */
  artifactDir?: string
  /** Whether to capture artifacts on failure */
  captureArtifacts?: boolean
  /** Maximum number of retained artifacts in artifactDir */
  maxArtifacts?: number
  /** Maximum artifact age in days before pruning */
  maxArtifactAgeDays?: number
}

const defaultConfig: HarnessConfig = {
  artifactDir: process.env["CICSC_CONFORMANCE_ARTIFACT_DIR"] || "./test-artifacts/conformance",
  captureArtifacts: process.env["CICSC_CAPTURE_ARTIFACTS"] !== "false",
  maxArtifacts: parseInt(process.env["CICSC_CONFORMANCE_MAX_ARTIFACTS"] || "200", 10),
  maxArtifactAgeDays: parseInt(process.env["CICSC_CONFORMANCE_MAX_ARTIFACT_AGE_DAYS"] || "14", 10),
}

function applyArtifactRetention (config: HarnessConfig = defaultConfig): void {
  if (!config.artifactDir) return
  if (!fs.existsSync(config.artifactDir)) return

  const maxArtifacts = Math.max(1, config.maxArtifacts ?? 200)
  const maxAgeDays = Math.max(1, config.maxArtifactAgeDays ?? 14)
  const cutoffMs = Date.now() - maxAgeDays * 24 * 60 * 60 * 1000

  const files = fs
    .readdirSync(config.artifactDir)
    .filter((name) => name.startsWith("replay-failure-seed-") && name.endsWith(".json"))
    .map((name) => {
      const fullPath = path.join(config.artifactDir!, name)
      const stat = fs.statSync(fullPath)
      return { name, fullPath, mtimeMs: stat.mtimeMs }
    })
    .sort((a, b) => b.mtimeMs - a.mtimeMs)

  for (const f of files) {
    if (f.mtimeMs < cutoffMs) {
      fs.unlinkSync(f.fullPath)
    }
  }

  const kept = fs
    .readdirSync(config.artifactDir)
    .filter((name) => name.startsWith("replay-failure-seed-") && name.endsWith(".json"))
    .map((name) => {
      const fullPath = path.join(config.artifactDir!, name)
      const stat = fs.statSync(fullPath)
      return { fullPath, mtimeMs: stat.mtimeMs }
    })
    .sort((a, b) => b.mtimeMs - a.mtimeMs)

  if (kept.length > maxArtifacts) {
    for (const f of kept.slice(maxArtifacts)) {
      fs.unlinkSync(f.fullPath)
    }
  }
}

/** Write replay artifact to disk for deterministic reproduction (P4.2.3) */
function writeFailureArtifact (
  artifact: ReplayArtifact,
  config: HarnessConfig = defaultConfig
): string | null {
  if (!config.captureArtifacts || !config.artifactDir) {
    return null
  }

  // Ensure artifact directory exists
  fs.mkdirSync(config.artifactDir, { recursive: true })
  applyArtifactRetention(config)

  // Generate unique filename based on seed and timestamp
  const timestamp = new Date().toISOString().replace(/[:.]/g, "-")
  const filename = `replay-failure-seed-${artifact.seed}-${timestamp}.json`
  const filepath = path.join(config.artifactDir, filename)

  // Write artifact
  fs.writeFileSync(filepath, JSON.stringify(artifact, null, 2), "utf-8")

  return filepath
}

/** Result from parity assertion with full diagnostic info */
export type ParityResult = {
  success: boolean
  seed?: number
  error?: string
  sqlRows?: any[]
  oracleRows?: any[]
  artifactPath?: string | null
}

export function assertSqliteOracleParity (
  query: any,
  snapRows: any[],
  seed?: number,
  config: HarnessConfig = defaultConfig
): ParityResult {
  const db = openSqliteMemory()
  try {
    installSqliteSchemaV0(db)
    for (const row of snapRows) {
      upsertSnapshot(db, {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: row.entity_id,
        state: row.state,
        attrs: {},
        updated_ts: 1,
        severity_i: row.severity_i ?? null,
        created_at: row.created_at ?? null,
      })
    }

    const plan = lowerQueryToSql(query, { version: 0, tenant_id: "t" })
    const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query, plan })
    const sqlProjected = sqlRows.map((r: any) => ({
      id: r.id,
      state: r.state,
      sev: r.sev,
    }))

    const oracle = interpretQuery(query, oracleCtx(snapRows) as any)

    try {
      assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
      return { success: true, seed }
    } catch (err: any) {
      // Capture failure artifact if seed is provided (P4.2.3)
      let artifactPath: string | null = null
      if (seed !== undefined) {
        const artifact = toReplayArtifact({ seed, query, snapRows }, "Ticket")
        artifactPath = writeFailureArtifact(artifact, config)
      }

      const result: ParityResult = {
        success: false,
        seed,
        error: err?.message ?? String(err),
        sqlRows: sqlProjected,
        oracleRows: oracle.rows,
        artifactPath,
      }

      // Enhance error message with artifact info
      const artifactMsg = artifactPath
        ? `\n\nReplay artifact written to: ${artifactPath}\nTo reproduce: CICSC_REPLAY_ARTIFACT=${artifactPath} npm test`
        : ""

      throw new Error(
        `SQLite/Oracle parity failure (seed: ${seed}): ${result.error}${artifactMsg}`
      )
    }
  } finally {
    db.close()
  }
}

/** Replay a conformance test from an artifact file (P4.2.3) */
export function replayFromArtifactFile (artifactPath: string): ParityResult {
  const json = fs.readFileSync(artifactPath, "utf-8")
  const artifact: ReplayArtifact = JSON.parse(json)

  // Validate version
  if (artifact.version !== "cicsc/conformance-replay-v1") {
    throw new Error(`Unsupported replay artifact version: ${artifact.version}`)
  }

  // Regenerate from artifact
  const regenerated = regenerateFromArtifact(artifact)

  // Run parity check
  return assertSqliteOracleParity(
    regenerated.query,
    regenerated.snapRows,
    regenerated.seed,
    { captureArtifacts: false } // Don't create artifacts during replay
  )
}
