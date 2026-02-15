type D1Database = {
  exec: (sql: string) => Promise<any>
  prepare: (sql: string) => {
    bind: (...args: any[]) => {
      run: () => Promise<any>
      first: <T = any>() => Promise<T | null>
      all: <T = any>() => Promise<{ results: T[] }>
    }
  }
}

export type TenantBinding = {
  tenant_id: string
  bundle_name: string
  bundle_version: string
  bundle_hash: string
  active_version: number
}

export type TenantBindingAuditRow = {
  audit_id: number
  tenant_id: string
  prev_bundle_name: string | null
  prev_bundle_version: string | null
  prev_bundle_hash: string | null
  prev_active_version: number | null
  next_bundle_name: string
  next_bundle_version: string
  next_bundle_hash: string
  next_active_version: number
  changed_ts: number
}

export async function ensureTenantBindingTable (db: D1Database): Promise<void> {
  await db.exec(`
    CREATE TABLE IF NOT EXISTS tenant_bindings (
      tenant_id      TEXT PRIMARY KEY,
      bundle_name    TEXT NOT NULL,
      bundle_version TEXT NOT NULL,
      bundle_hash    TEXT NOT NULL,
      active_version INTEGER NOT NULL,
      updated_ts     INTEGER NOT NULL
    );
  `)
}

export async function ensureTenantBindingAuditTable (db: D1Database): Promise<void> {
  await db.exec(`
    CREATE TABLE IF NOT EXISTS tenant_binding_audit (
      audit_id             INTEGER PRIMARY KEY AUTOINCREMENT,
      tenant_id            TEXT NOT NULL,
      prev_bundle_name     TEXT,
      prev_bundle_version  TEXT,
      prev_bundle_hash     TEXT,
      prev_active_version  INTEGER,
      next_bundle_name     TEXT NOT NULL,
      next_bundle_version  TEXT NOT NULL,
      next_bundle_hash     TEXT NOT NULL,
      next_active_version  INTEGER NOT NULL,
      changed_ts           INTEGER NOT NULL
    );
  `)
}

export async function bindTenant (db: D1Database, params: {
  tenant_id: string
  bundle_name: string
  bundle_version: string
  bundle_hash: string
  active_version: number
}): Promise<void> {
  await ensureTenantBindingTable(db)
  await ensureTenantBindingAuditTable(db)
  const ts = nowUnix()
  const prev = await getTenantBinding(db, params.tenant_id)
  await db
    .prepare(
      `INSERT INTO tenant_bindings(tenant_id, bundle_name, bundle_version, bundle_hash, active_version, updated_ts)
       VALUES(?,?,?,?,?,?)
       ON CONFLICT(tenant_id) DO UPDATE SET
         bundle_name=excluded.bundle_name,
         bundle_version=excluded.bundle_version,
         bundle_hash=excluded.bundle_hash,
         active_version=excluded.active_version,
         updated_ts=excluded.updated_ts`
    )
    .bind(params.tenant_id, params.bundle_name, params.bundle_version, params.bundle_hash, params.active_version, ts)
    .run()

  await db
    .prepare(
      `INSERT INTO tenant_binding_audit(
         tenant_id, 
         prev_bundle_name, prev_bundle_version, prev_bundle_hash, prev_active_version, 
         next_bundle_name, next_bundle_version, next_bundle_hash, next_active_version, 
         changed_ts
       ) VALUES(?,?,?,?,?,?,?,?,?,?)`
    )
    .bind(
      params.tenant_id,
      prev?.bundle_name ?? null,
      prev?.bundle_version ?? null,
      prev?.bundle_hash ?? null,
      prev?.active_version ?? null,
      params.bundle_name,
      params.bundle_version,
      params.bundle_hash,
      params.active_version,
      ts
    )
    .run()
}

export async function getTenantBinding (db: D1Database, tenant_id: string): Promise<TenantBinding | null> {
  await ensureTenantBindingTable(db)
  const row = await db
    .prepare(
      `SELECT tenant_id, bundle_name, bundle_version, bundle_hash, active_version
       FROM tenant_bindings
       WHERE tenant_id=?
       LIMIT 1`
    )
    .bind(tenant_id)
    .first<TenantBinding>()
  return row ?? null
}

export async function unbindTenant (db: D1Database, tenant_id: string): Promise<void> {
  await ensureTenantBindingTable(db)
  await ensureTenantBindingAuditTable(db)
  const ts = nowUnix()
  const prev = await getTenantBinding(db, tenant_id)
  if (!prev) return

  await db
    .prepare(`DELETE FROM tenant_bindings WHERE tenant_id=?`)
    .bind(tenant_id)
    .run()

  await db
    .prepare(
      `INSERT INTO tenant_binding_audit(
         tenant_id, 
         prev_bundle_name, prev_bundle_version, prev_bundle_hash, prev_active_version, 
         next_bundle_name, next_bundle_version, next_bundle_hash, next_active_version, 
         changed_ts
       ) VALUES(?,?,?,?,?,?,?,?,?,?)`
    )
    .bind(
      tenant_id,
      prev.bundle_name,
      prev.bundle_version,
      prev.bundle_hash,
      prev.active_version,
      "DELETED",
      "0.0.0",
      "NONE",
      0,
      ts
    )
    .run()
}

export async function listTenantBindingAudit (db: D1Database, tenant_id: string): Promise<TenantBindingAuditRow[]> {
  await ensureTenantBindingAuditTable(db)
  const rows = await db
    .prepare(
      `SELECT
         audit_id,
         tenant_id,
         prev_bundle_name,
         prev_bundle_version,
         prev_bundle_hash,
         prev_active_version,
         next_bundle_name,
         next_bundle_version,
         next_bundle_hash,
         next_active_version,
         changed_ts
       FROM tenant_binding_audit
       WHERE tenant_id=?
       ORDER BY audit_id ASC`
    )
    .bind(tenant_id)
    .all<TenantBindingAuditRow>()

  return rows?.results ?? []
}

function nowUnix (): number {
  return Math.floor(Date.now() / 1000)
}
