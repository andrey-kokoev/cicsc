type D1Database = {
  exec: (sql: string) => Promise<any>
  prepare: (sql: string) => {
    bind: (...args: any[]) => {
      run: () => Promise<any>
      first: <T = any>() => Promise<T | null>
    }
  }
}

export type TenantBinding = {
  tenant_id: string
  bundle_hash: string
  active_version: number
}

export async function ensureTenantBindingTable (db: D1Database): Promise<void> {
  await db.exec(`
    CREATE TABLE IF NOT EXISTS tenant_bindings (
      tenant_id      TEXT PRIMARY KEY,
      bundle_hash    TEXT NOT NULL,
      active_version INTEGER NOT NULL,
      updated_ts     INTEGER NOT NULL
    );
  `)
}

export async function bindTenant (db: D1Database, params: {
  tenant_id: string
  bundle_hash: string
  active_version: number
}): Promise<void> {
  await ensureTenantBindingTable(db)
  await db
    .prepare(
      `INSERT INTO tenant_bindings(tenant_id, bundle_hash, active_version, updated_ts)
       VALUES(?,?,?,?)
       ON CONFLICT(tenant_id) DO UPDATE SET
         bundle_hash=excluded.bundle_hash,
         active_version=excluded.active_version,
         updated_ts=excluded.updated_ts`
    )
    .bind(params.tenant_id, params.bundle_hash, params.active_version, nowUnix())
    .run()
}

export async function getTenantBinding (db: D1Database, tenant_id: string): Promise<TenantBinding | null> {
  await ensureTenantBindingTable(db)
  const row = await db
    .prepare(
      `SELECT tenant_id, bundle_hash, active_version
       FROM tenant_bindings
       WHERE tenant_id=?
       LIMIT 1`
    )
    .bind(tenant_id)
    .first<TenantBinding>()
  return row ?? null
}

function nowUnix (): number {
  return Math.floor(Date.now() / 1000)
}
