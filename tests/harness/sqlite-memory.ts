// /tests/harness/sqlite-memory.ts

import { createRequire } from "node:module"
import { fileURLToPath } from "node:url"

import type { SqlPlan } from "../../adapters/sqlite/src/lower/query-to-sql"
import type { QueryV0, SourceV0 } from "../../core/ir/types"

type Db = {
  exec: (sql: string) => void
  prepare: (sql: string) => {
    all: (binds?: any[]) => any[]
    get: (binds?: any[]) => any
    run: (binds?: any[]) => any
  }
  close: () => void
}

export function openSqliteMemory (): Db {
  const require = createRequire(import.meta.url)
  // Prefer better-sqlite3 (sync, simple) from normal resolution first, then
  // the phase3 harness dependency bundle for deterministic local/CI usage.
  try {
    let BetterSqlite3: any
    try {
      BetterSqlite3 = require("better-sqlite3")
    } catch {
      const bundledPath = fileURLToPath(new URL("../harness-deps/node_modules/better-sqlite3", import.meta.url))
      BetterSqlite3 = require(bundledPath)
    }
    const db = new BetterSqlite3(":memory:")
    db.pragma("foreign_keys = ON")
    return {
      exec: (sql) => db.exec(sql),
      prepare: (sql) => {
        const stmt = db.prepare(sql)
        return {
          all: (binds = []) => stmt.all(...binds),
          get: (binds = []) => stmt.get(...binds),
          run: (binds = []) => stmt.run(...binds),
        }
      },
      close: () => db.close(),
    }
  } catch {
    throw new Error(
      "sqlite harness needs a local sqlite driver. Add devDependency: better-sqlite3, then re-run tests."
    )
  }
}

export function installSqliteSchemaV0 (db: Db) {
  db.exec(`
    CREATE TABLE IF NOT EXISTS snapshots_v0 (
      tenant_id   TEXT NOT NULL,
      entity_type TEXT NOT NULL,
      entity_id   TEXT NOT NULL,
      state       TEXT NOT NULL,
      attrs_json  TEXT NOT NULL,
      updated_ts  INTEGER NOT NULL,
      severity_i  INTEGER,
      created_at  INTEGER,
      PRIMARY KEY (tenant_id, entity_type, entity_id)
    );

    CREATE TABLE IF NOT EXISTS sla_status (
      tenant_id   TEXT NOT NULL,
      name        TEXT NOT NULL,
      entity_type TEXT NOT NULL,
      entity_id   TEXT NOT NULL,
      start_ts    INTEGER,
      stop_ts     INTEGER,
      deadline_ts INTEGER,
      breached    INTEGER NOT NULL,
      updated_ts  INTEGER NOT NULL,
      PRIMARY KEY (tenant_id, name, entity_type, entity_id)
    );
  `)
}

export function upsertSnapshot (db: Db, row: {
  tenant_id: string
  entity_type: string
  entity_id: string
  state: string
  attrs: Record<string, any>
  updated_ts: number
  severity_i?: number | null
  created_at?: number | null
}) {
  db.prepare(
    `INSERT INTO snapshots_v0(tenant_id, entity_type, entity_id, state, attrs_json, updated_ts, severity_i, created_at)
     VALUES(?,?,?,?,?,?,?,?)
     ON CONFLICT(tenant_id, entity_type, entity_id) DO UPDATE SET
       state=excluded.state,
       attrs_json=excluded.attrs_json,
       updated_ts=excluded.updated_ts,
       severity_i=excluded.severity_i,
       created_at=excluded.created_at`
  ).run([
    row.tenant_id,
    row.entity_type,
    row.entity_id,
    row.state,
    JSON.stringify(row.attrs ?? {}),
    row.updated_ts,
    row.severity_i ?? null,
    row.created_at ?? null,
  ])
}

export function upsertSlaStatus (db: Db, row: {
  tenant_id: string
  name: string
  entity_type: string
  entity_id: string
  breached: 0 | 1
  deadline_ts?: number | null
  start_ts?: number | null
  stop_ts?: number | null
  updated_ts: number
}) {
  db.prepare(
    `INSERT INTO sla_status(tenant_id, name, entity_type, entity_id, start_ts, stop_ts, deadline_ts, breached, updated_ts)
     VALUES(?,?,?,?,?,?,?,?,?)
     ON CONFLICT(tenant_id, name, entity_type, entity_id) DO UPDATE SET
       start_ts=excluded.start_ts,
       stop_ts=excluded.stop_ts,
       deadline_ts=excluded.deadline_ts,
       breached=excluded.breached,
       updated_ts=excluded.updated_ts`
  ).run([
    row.tenant_id,
    row.name,
    row.entity_type,
    row.entity_id,
    row.start_ts ?? null,
    row.stop_ts ?? null,
    row.deadline_ts ?? null,
    row.breached,
    row.updated_ts,
  ])
}

export function runPlanAll (db: Db, sql: string, binds: any[]) {
  return db.prepare(sql).all(binds)
}

export function runLoweredQueryPlan (db: Db, params: { tenant_id: string; query: QueryV0; plan: SqlPlan }) {
  const sourceBinds = inferSourceBinds(params.query.source, params.tenant_id)
  return runPlanAll(db, params.plan.sql, [...sourceBinds, ...params.plan.binds])
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
