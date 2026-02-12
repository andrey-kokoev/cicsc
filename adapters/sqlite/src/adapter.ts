import { withImmediateTx, type TxCtx } from "./tx"
import type {
  AppendResult,
  Capabilities,
  CommandId,
  ConstraintCtx,
  EntityId,
  EntityType,
  EventRecord,
  EventRow,
  SnapshotRow,
  SlaBreach,
  StreamCursor,
  TenantId,
  UnixSeconds,
  ViewResultPage,
} from "./types"

type D1Database = {
  prepare (sql: string): D1PreparedStatement
  batch<T = unknown> (stmts: D1PreparedStatement[]): Promise<D1Result<T>[]>
  exec (sql: string): Promise<D1ExecResult>
}
type D1PreparedStatement = {
  bind (...values: any[]): D1PreparedStatement
  first<T = any> (): Promise<T | null>
  all<T = any> (): Promise<{ results: T[] }>
  run<T = any> (): Promise<D1Result<T>>
}
type D1Result<T> = { success: boolean; meta: any; results?: T[] }
type D1ExecResult = { count: number; duration: number }

export class SqliteD1Adapter {
  readonly caps: Capabilities = {
    transactions: { atomic_batch_append: true, snapshot_in_same_tx: true },
    query: { joins: true, secondary_indexes: "limited", json_extract: "limited" },
    constraints: { snapshot_vm: true, bool_query: true },
    projections: { query_time: true, materialized: true },
    scheduler: { cron: true },
  };

  constructor(private readonly db: D1Database) { }

  async tx<T> (fn: (tx: TxCtx) => Promise<T>): Promise<T> {
    return withImmediateTx(this.db as any, fn)
  }

  // --------------------------
  // Versioning
  // --------------------------

  async get_active_version (tenant_id: TenantId): Promise<number> {
    const row = await this.db
      .prepare(`SELECT active_version FROM tenant_versions WHERE tenant_id=?`)
      .bind(tenant_id)
      .first<{ active_version: number }>()
    return row?.active_version ?? 0
  }

  async set_active_version (tenant_id: TenantId, version: number): Promise<void> {
    await this.tx(async (tx) => {
      await tx.exec(
        `INSERT INTO tenant_versions(tenant_id, active_version) VALUES(?,?)
         ON CONFLICT(tenant_id) DO UPDATE SET active_version=excluded.active_version`,
        [tenant_id, version]
      )
    })
  }

  // --------------------------
  // Events
  // --------------------------

  async append_events (params: {
    tenant_id: TenantId
    entity_type: EntityType
    entity_id: EntityId
    command_id: CommandId
    events: EventRecord[]
  }): Promise<AppendResult> {
    const { tenant_id, entity_type, entity_id, command_id, events } = params
    if (events.length === 0) throw new Error("append_events: empty batch")

    return this.tx(async (tx) => {
      // Idempotency: if receipt exists, return it.
      const receipt = firstRow<{ result_json: string }>(
        await tx.exec(
          `SELECT result_json FROM command_receipts WHERE tenant_id=? AND command_id=?`,
          [tenant_id, command_id]
        )
      )

      if (receipt?.result_json) {
        return JSON.parse(receipt.result_json) as AppendResult
      }

      // Compute next seq and append in the same explicit tx boundary.
      const ver = await this.get_active_version_tx(tx, tenant_id)
      const eventsTable = `events_v${ver}`
      const snapshotsTable = `snapshots_v${ver}`

      const maxRow = firstRow<{ max_seq: number }>(
        await tx.exec(
          `SELECT COALESCE(MAX(seq), 0) AS max_seq FROM ${eventsTable}
           WHERE tenant_id=? AND entity_type=? AND entity_id=?`,
          [tenant_id, entity_type, entity_id]
        )
      )
      const seqStart = (maxRow?.max_seq ?? 0) + 1

      for (let i = 0; i < events.length; i++) {
        const e = events[i]!
        const seq = seqStart + i
        await tx.exec(
          `INSERT INTO ${eventsTable}
           (tenant_id, entity_type, entity_id, seq, event_type, payload_json, ts, actor_id)
           VALUES (?,?,?,?,?,?,?,?)`,
          [
            tenant_id,
            entity_type,
            entity_id,
            seq,
            e.event_type,
            JSON.stringify(e.payload ?? null),
            e.ts,
            e.actor_id,
          ]
        )
      }

      const result: AppendResult = { entity_id, seq_from: seqStart, seq_to: seqStart + events.length - 1 }

      await tx.exec(
        `INSERT INTO command_receipts(tenant_id, command_id, entity_type, entity_id, result_json, ts)
         VALUES (?,?,?,?,?,?)
         ON CONFLICT(tenant_id, command_id) DO NOTHING`,
        [tenant_id, command_id, entity_type, entity_id, JSON.stringify(result), nowUnix()]
      )

      // Ensure snapshot row exists (runtime will overwrite full snapshot after reducer)
      await tx.exec(
        `INSERT INTO ${snapshotsTable}(tenant_id, entity_type, entity_id, state, attrs_json, updated_ts)
         VALUES (?,?,?,?,?,?)
         ON CONFLICT(tenant_id, entity_type, entity_id) DO NOTHING`,
        [tenant_id, entity_type, entity_id, "new", "{}", nowUnix()]
      )

      return result
    })
  }

  async read_stream (params: {
    tenant_id: TenantId
    entity_type: EntityType
    entity_id: EntityId
    from?: StreamCursor
    limit?: number
  }): Promise<{ events: EventRow[]; next?: StreamCursor }> {
    const { tenant_id, entity_type, entity_id, from, limit } = params
    const ver = await this.get_active_version(tenant_id)
    const eventsTable = `events_v${ver}`
    const lim = Math.max(1, Math.min(limit ?? 500, 2000))
    const fromSeq = from?.seq ?? 0

    const rows = await this.db
      .prepare(
        `SELECT tenant_id, entity_type, entity_id, seq, event_type, payload_json, ts, actor_id
         FROM ${eventsTable}
         WHERE tenant_id=? AND entity_type=? AND entity_id=? AND seq>?
         ORDER BY seq ASC
         LIMIT ?`
      )
      .bind(tenant_id, entity_type, entity_id, fromSeq, lim)
      .all<EventRow>()

    const events = rows.results ?? []
    const next = events.length === lim ? { seq: events[events.length - 1]!.seq } : undefined
    return { events, next }
  }

  // --------------------------
  // Snapshots
  // --------------------------

  async get_snapshot (params: {
    tenant_id: TenantId
    entity_type: EntityType
    entity_id: EntityId
  }): Promise<SnapshotRow | null> {
    const { tenant_id, entity_type, entity_id } = params
    const ver = await this.get_active_version(tenant_id)
    const snapshotsTable = `snapshots_v${ver}`
    return await this.db
      .prepare(
        `SELECT tenant_id, entity_type, entity_id, state, attrs_json, updated_ts
         FROM ${snapshotsTable}
         WHERE tenant_id=? AND entity_type=? AND entity_id=?`
      )
      .bind(tenant_id, entity_type, entity_id)
      .first<SnapshotRow>()
  }

  async put_snapshot (params: {
    tenant_id: TenantId
    entity_type: EntityType
    entity_id: EntityId
    state: string
    attrs_json: string // canonical JSON
    updated_ts: UnixSeconds
    shadows?: Record<string, string | number | null>
  }): Promise<void> {
    const { tenant_id, entity_type, entity_id, state, attrs_json, updated_ts, shadows } = params
    await this.tx(async (tx) => {
      const ver = await this.get_active_version_tx(tx, tenant_id)
      const snapshotsTable = `snapshots_v${ver}`

      const shadowCols = shadows ? Object.keys(shadows) : []
      const setShadowSql =
        shadowCols.length === 0
          ? ""
          : ", " +
          shadowCols
            .map((c) => `${escapeIdent(c)}=?`)
            .join(", ")

      const bindShadowVals = shadowCols.map((c) => (shadows as any)[c])

      const sql =
        `UPDATE ${snapshotsTable}
         SET state=?, attrs_json=?, updated_ts=?` +
        setShadowSql +
        ` WHERE tenant_id=? AND entity_type=? AND entity_id=?`

      await tx.exec(sql, [state, attrs_json, updated_ts, ...bindShadowVals, tenant_id, entity_type, entity_id])
    })
  }

  // --------------------------
  // Constraints (bool_query is lowered by compiler into SQL templates per adapter)
  // --------------------------

  async eval_constraint_sql (params: {
    tenant_id: TenantId
    sql: string
    binds: any[]
    ctx: ConstraintCtx
  }): Promise<boolean> {
    const row = await this.db.prepare(params.sql).bind(...params.binds).first<{ ok: number | boolean }>()
    if (row == null) throw new Error("eval_constraint_sql: no result")
    return row.ok === 1 || row.ok === true
  }

  // --------------------------
  // Views (compiler lowers View Query AST to SQL + bind list)
  // --------------------------

  async exec_view_sql (params: { sql: string; binds: any[] }): Promise<ViewResultPage> {
    const r = await this.db.prepare(params.sql).bind(...params.binds).all<any>()
    return { rows: r.results ?? [] }
  }

  // --------------------------
  // SLA (minimal table operations; higher-level SLA logic is in runtime/projector)
  // --------------------------

  async sla_upsert_status (params: {
    tenant_id: TenantId
    name: string
    entity_type: EntityType
    entity_id: EntityId
    start_ts?: UnixSeconds | null
    stop_ts?: UnixSeconds | null
    deadline_ts?: UnixSeconds | null
    breached: 0 | 1
    updated_ts: UnixSeconds
  }): Promise<void> {
    const p = params
    await this.tx(async (tx) => {
      await tx.exec(
        `INSERT INTO sla_status(tenant_id,name,entity_type,entity_id,start_ts,stop_ts,deadline_ts,breached,updated_ts)
         VALUES (?,?,?,?,?,?,?,?,?)
         ON CONFLICT(tenant_id,name,entity_type,entity_id)
         DO UPDATE SET
           start_ts=COALESCE(excluded.start_ts, sla_status.start_ts),
           stop_ts=COALESCE(excluded.stop_ts, sla_status.stop_ts),
           deadline_ts=COALESCE(excluded.deadline_ts, sla_status.deadline_ts),
           breached=excluded.breached,
           updated_ts=excluded.updated_ts`,
        [
          p.tenant_id,
          p.name,
          p.entity_type,
          p.entity_id,
          p.start_ts ?? null,
          p.stop_ts ?? null,
          p.deadline_ts ?? null,
          p.breached,
          p.updated_ts,
        ]
      )
    })
  }

  async sla_check_due (params: {
    tenant_id: TenantId
    name: string
    now: UnixSeconds
    limit: number
  }): Promise<SlaBreach[]> {
    const lim = Math.max(1, Math.min(params.limit, 1000))
    const rows = await this.db
      .prepare(
        `SELECT tenant_id, name, entity_type, entity_id, deadline_ts
         FROM sla_status
         WHERE tenant_id=? AND name=? AND breached=0 AND stop_ts IS NULL AND deadline_ts IS NOT NULL AND deadline_ts < ?
         ORDER BY deadline_ts ASC
         LIMIT ?`
      )
      .bind(params.tenant_id, params.name, params.now, lim)
      .all<SlaBreach>()
    return rows.results ?? []
  }

  async sla_mark_breached (params: {
    tenant_id: TenantId
    name: string
    entity_type: EntityType
    entity_id: EntityId
    now: UnixSeconds
  }): Promise<void> {
    await this.tx(async (tx) => {
      await tx.exec(
        `UPDATE sla_status
         SET breached=1, updated_ts=?
         WHERE tenant_id=? AND name=? AND entity_type=? AND entity_id=?`,
        [params.now, params.tenant_id, params.name, params.entity_type, params.entity_id]
      )
    })
  }

  private async get_active_version_tx (tx: TxCtx, tenant_id: TenantId): Promise<number> {
    const row = firstRow<{ active_version: number }>(
      await tx.exec(`SELECT active_version FROM tenant_versions WHERE tenant_id=?`, [tenant_id])
    )
    return row?.active_version ?? 0
  }
}

function nowUnix (): UnixSeconds {
  return Math.floor(Date.now() / 1000)
}

function escapeIdent (name: string): string {
  // Very strict identifier policy: letters, digits, underscore only.
  // Compiler MUST generate shadow names that pass this.
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new Error(`Invalid identifier: ${name}`)
  return name
}

function firstRow<T> (r: { rows?: any[] }): T | null {
  return (r.rows?.[0] as T | undefined) ?? null
}
