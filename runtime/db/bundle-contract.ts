import type { CoreIrBundleV0 } from "../../core/ir/types"
import { getBundle, putBundle } from "./bundle-registry"

type D1Database = {
  exec: (sql: string) => Promise<any>
  prepare: (sql: string) => {
    bind: (...args: any[]) => {
      run: () => Promise<any>
      first: <T = any>() => Promise<T | null>
    }
  }
}

export async function ensureBundlePinsTable (db: D1Database): Promise<void> {
  await db.exec(`
    CREATE TABLE IF NOT EXISTS bundle_pins (
      pin_name    TEXT PRIMARY KEY,
      bundle_hash TEXT NOT NULL,
      created_ts  INTEGER NOT NULL,
      updated_ts  INTEGER NOT NULL
    );
  `)
}

export async function publishBundle (db: D1Database, bundle: CoreIrBundleV0): Promise<{ bundle_hash: string }> {
  return putBundle(db, bundle)
}

export async function resolveBundle (db: D1Database, bundle_hash: string): Promise<CoreIrBundleV0 | null> {
  return getBundle(db, bundle_hash)
}

export async function pinBundle (db: D1Database, pin_name: string, bundle_hash: string): Promise<void> {
  await ensureBundlePinsTable(db)
  const ts = nowUnix()
  await db
    .prepare(
      `INSERT INTO bundle_pins(pin_name, bundle_hash, created_ts, updated_ts)
       VALUES(?,?,?,?)
       ON CONFLICT(pin_name) DO UPDATE SET
         bundle_hash=excluded.bundle_hash,
         updated_ts=excluded.updated_ts`
    )
    .bind(pin_name, bundle_hash, ts, ts)
    .run()
}

export async function resolvePinnedBundle (db: D1Database, pin_name: string): Promise<{ bundle_hash: string; bundle: CoreIrBundleV0 } | null> {
  await ensureBundlePinsTable(db)
  const row = await db
    .prepare(`SELECT bundle_hash FROM bundle_pins WHERE pin_name=? LIMIT 1`)
    .bind(pin_name)
    .first<{ bundle_hash: string }>()
  if (!row?.bundle_hash) return null

  const bundle = await resolveBundle(db, row.bundle_hash)
  if (!bundle) return null
  return { bundle_hash: row.bundle_hash, bundle }
}

function nowUnix (): number {
  return Math.floor(Date.now() / 1000)
}
