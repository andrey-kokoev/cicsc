import type { SqlPlan } from "../../adapters/postgres/src/lower/query-to-sql"
import type { QueryV0, SourceV0 } from "../../core/ir/types"

type PoolLike = {
  query: (sql: string, binds?: any[]) => Promise<{ rows: any[] }>
  end: () => Promise<void>
}

export async function openPgMemory (): Promise<{ pool: PoolLike; close: () => Promise<void> }> {
  try {
    // eslint-disable-next-line @typescript-eslint/no-var-requires
    const { newDb } = require("pg-mem")
    const db = newDb()
    const { Pool } = db.adapters.createPg()
    const pool: PoolLike = new Pool()
    return {
      pool,
      close: async () => {
        await pool.end()
      },
    }
  } catch {
    throw new Error("postgres harness needs a local postgres driver. Add devDependency: pg-mem, then re-run tests.")
  }
}

export async function installPostgresSchemaV0 (pool: PoolLike): Promise<void> {
  await pool.query(`
    CREATE TABLE IF NOT EXISTS snapshots_v0 (
      tenant_id   TEXT NOT NULL,
      entity_type TEXT NOT NULL,
      entity_id   TEXT NOT NULL,
      state       TEXT NOT NULL,
      attrs       JSONB NOT NULL,
      updated_ts  BIGINT NOT NULL,
      severity_i  BIGINT,
      created_at  BIGINT,
      PRIMARY KEY (tenant_id, entity_type, entity_id)
    );

    CREATE TABLE IF NOT EXISTS sla_status (
      tenant_id   TEXT NOT NULL,
      name        TEXT NOT NULL,
      entity_type TEXT NOT NULL,
      entity_id   TEXT NOT NULL,
      start_ts    BIGINT,
      stop_ts     BIGINT,
      deadline_ts BIGINT,
      breached    BOOLEAN NOT NULL,
      updated_ts  BIGINT NOT NULL,
      PRIMARY KEY (tenant_id, name, entity_type, entity_id)
    );
  `)
}

export async function upsertSnapshot (pool: PoolLike, row: {
  tenant_id: string
  entity_type: string
  entity_id: string
  state: string
  attrs: Record<string, any>
  updated_ts: number
  severity_i?: number | null
  created_at?: number | null
}) {
  await pool.query(
    `INSERT INTO snapshots_v0(tenant_id, entity_type, entity_id, state, attrs, updated_ts, severity_i, created_at)
     VALUES($1,$2,$3,$4,$5::jsonb,$6,$7,$8)
     ON CONFLICT(tenant_id, entity_type, entity_id) DO UPDATE SET
       state=excluded.state,
       attrs=excluded.attrs,
       updated_ts=excluded.updated_ts,
       severity_i=excluded.severity_i,
       created_at=excluded.created_at`,
    [
      row.tenant_id,
      row.entity_type,
      row.entity_id,
      row.state,
      JSON.stringify(row.attrs ?? {}),
      row.updated_ts,
      row.severity_i ?? null,
      row.created_at ?? null,
    ]
  )
}

export async function upsertSlaStatus (pool: PoolLike, row: {
  tenant_id: string
  name: string
  entity_type: string
  entity_id: string
  breached: boolean
  deadline_ts?: number | null
  start_ts?: number | null
  stop_ts?: number | null
  updated_ts: number
}) {
  await pool.query(
    `INSERT INTO sla_status(tenant_id, name, entity_type, entity_id, start_ts, stop_ts, deadline_ts, breached, updated_ts)
     VALUES($1,$2,$3,$4,$5,$6,$7,$8,$9)
     ON CONFLICT(tenant_id, name, entity_type, entity_id) DO UPDATE SET
       start_ts=excluded.start_ts,
       stop_ts=excluded.stop_ts,
       deadline_ts=excluded.deadline_ts,
       breached=excluded.breached,
       updated_ts=excluded.updated_ts`,
    [
      row.tenant_id,
      row.name,
      row.entity_type,
      row.entity_id,
      row.start_ts ?? null,
      row.stop_ts ?? null,
      row.deadline_ts ?? null,
      row.breached,
      row.updated_ts,
    ]
  )
}

export async function runPlanAll (pool: PoolLike, sql: string, binds: any[]) {
  const r = await pool.query(sql, binds)
  return r.rows
}

export async function runLoweredQueryPlan (pool: PoolLike, params: { tenant_id: string; query: QueryV0; plan: SqlPlan }) {
  const sourceBinds = inferSourceBinds(params.query.source, params.tenant_id)
  return runPlanAll(pool, params.plan.sql, [...sourceBinds, ...params.plan.binds])
}

function inferSourceBinds (src: SourceV0, tenant_id: string): any[] {
  const tag = soleKey(src as any)
  const body: any = (src as any)[tag]

  if (tag === "snap") return [tenant_id, String(body.type)]
  if (tag === "sla_status") return [tenant_id, String(body.name), String(body.on_type)]
  if (tag === "join") return [...inferSourceBinds(body.left, tenant_id), ...inferSourceBinds(body.right, tenant_id)]
  throw new Error(`inferSourceBinds: unsupported source tag ${tag}`)
}

function soleKey (o: any): string {
  const ks = Object.keys(o)
  if (ks.length !== 1) throw new Error("invalid tagged object")
  return ks[0]!
}
