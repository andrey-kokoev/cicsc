import { createHash } from "node:crypto"

import type { CoreIrBundleV0 } from "../../core/ir/types"
import { validateBundleV0 } from "../../core/ir/validate"

type D1Database = {
  exec: (sql: string) => Promise<any>
  prepare: (sql: string) => {
    bind: (...args: any[]) => {
      run: () => Promise<any>
      first: <T = any>() => Promise<T | null>
    }
  }
}

export async function ensureBundleRegistryTable (db: D1Database): Promise<void> {
  await db.exec(`
    CREATE TABLE IF NOT EXISTS bundle_registry (
      bundle_hash TEXT PRIMARY KEY,
      bundle_json TEXT NOT NULL,
      created_ts  INTEGER NOT NULL
    );
  `)
}

export function bundleHash (bundle: CoreIrBundleV0): string {
  const canonical = stableJson(bundle)
  return createHash("sha256").update(canonical).digest("hex")
}

export async function putBundle (db: D1Database, bundle: CoreIrBundleV0): Promise<{ bundle_hash: string }> {
  await ensureBundleRegistryTable(db)
  const bundle_hash = bundleHash(bundle)

  await db
    .prepare(
      `INSERT INTO bundle_registry(bundle_hash, bundle_json, created_ts)
       VALUES(?,?,?)
       ON CONFLICT(bundle_hash) DO NOTHING`
    )
    .bind(bundle_hash, stableJson(bundle), nowUnix())
    .run()

  return { bundle_hash }
}

export async function getBundle (db: D1Database, bundle_hash: string): Promise<CoreIrBundleV0 | null> {
  await ensureBundleRegistryTable(db)
  const row = await db
    .prepare(`SELECT bundle_json FROM bundle_registry WHERE bundle_hash=? LIMIT 1`)
    .bind(bundle_hash)
    .first<{ bundle_json: string }>()
  if (!row?.bundle_json) return null

  const parsed = JSON.parse(row.bundle_json)
  const v = validateBundleV0(parsed)
  if (!v.ok) throw new Error(`bundle registry contains invalid bundle for hash=${bundle_hash}`)
  return v.value
}

function stableJson (v: any): string {
  return JSON.stringify(sortKeys(v))
}

function sortKeys (v: any): any {
  if (v === null || typeof v !== "object") return v
  if (Array.isArray(v)) return v.map(sortKeys)
  const out: any = {}
  for (const k of Object.keys(v).sort()) out[k] = sortKeys(v[k])
  return out
}

function nowUnix (): number {
  return Math.floor(Date.now() / 1000)
}
