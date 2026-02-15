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
  ScheduledJob,
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

  private readonly db: D1Database
  constructor(db: D1Database) {
    this.db = db
  }

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

  async read_tenant_events (params: {
    tenant_id: TenantId
    limit?: number
  }): Promise<EventRow[]> {
    const { tenant_id, limit } = params
    const ver = await this.get_active_version(tenant_id)
    const eventsTable = `events_v${ver}`
    const lim = Math.max(1, Math.min(limit ?? 50000, 200000))

    const rows = await this.db
      .prepare(
        `SELECT tenant_id, entity_type, entity_id, seq, event_type, payload_json, ts, actor_id
         FROM ${eventsTable}
         WHERE tenant_id=?
         ORDER BY entity_type ASC, entity_id ASC, seq ASC
         LIMIT ?`
      )
      .bind(tenant_id, lim)
      .all<EventRow>()

    return rows.results ?? []
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

  // --------------------------
  // Queues
  // --------------------------

  async enqueue (params: {
    tenant_id: TenantId
    queue_name: string
    message: any
    idempotency_key?: string
  }): Promise<void> {
    const { tenant_id, queue_name, message, idempotency_key } = params
    const message_json = JSON.stringify(message)
    const now = Date.now()
    const table = `queue_${escapeIdent(queue_name)}`

    await this.tx(async (tx) => {
      await tx.exec(
        `INSERT INTO ${table} (tenant_id, id, message_json, idempotency_key, created_at, updated_at, visible_after)
         VALUES (?, ?, ?, ?, ?, ?, ?)`,
        [tenant_id, crypto.randomUUID(), message_json, idempotency_key, now, now, now]
      )
    })
  }

  async dequeue (params: {
    tenant_id: TenantId
    queue_name: string
    visibility_timeout_ms: number
  }): Promise<any | null> {
    const { tenant_id, queue_name, visibility_timeout_ms } = params
    const table = `queue_${escapeIdent(queue_name)}`
    const now = Date.now()
    const visible_after = now + visibility_timeout_ms

    return this.tx(async (tx) => {
      const row = firstRow<any>(
        await tx.exec(
          `SELECT id, message_json, attempts, created_at 
           FROM ${table} 
           WHERE tenant_id=? AND visible_after <= ? 
           ORDER BY visible_after ASC, created_at ASC 
           LIMIT 1`,
          [tenant_id, now]
        )
      )

      if (!row) return null

      await tx.exec(
        `UPDATE ${table} 
         SET visible_after=?, attempts=attempts+1, updated_at=? 
         WHERE tenant_id=? AND id=?`,
        [visible_after, now, tenant_id, row.id]
      )

      return {
        id: row.id,
        payload: JSON.parse(row.message_json),
        attempts: row.attempts + 1,
        visible_after,
        created_at: row.created_at,
      }
    })
  }

  async ack (params: {
    tenant_id: TenantId
    queue_name: string
    message_id: string
  }): Promise<void> {
    const { tenant_id, queue_name, message_id } = params
    const table = `queue_${escapeIdent(queue_name)}`

    await this.tx(async (tx) => {
      await tx.exec(
        `DELETE FROM ${table} WHERE tenant_id=? AND id=?`,
        [tenant_id, message_id]
      )
    })
  }

  async retry (params: {
    tenant_id: TenantId
    queue_name: string
    message_id: string
    delay_ms: number
  }): Promise<void> {
    const { tenant_id, queue_name, message_id, delay_ms } = params
    const table = `queue_${escapeIdent(queue_name)}`
    const now = Date.now()
    const visible_after = now + delay_ms

    await this.tx(async (tx) => {
      await tx.exec(
        `UPDATE ${table} SET visible_after=?, updated_at=? WHERE tenant_id=? AND id=?`,
        [visible_after, now, tenant_id, message_id]
      )
    })
  }

  async deadLetter (params: {
    tenant_id: TenantId
    queue_name: string
    message_id: string
    error: string
  }): Promise<void> {
    const { tenant_id, queue_name, message_id, error } = params
    const table = `queue_${escapeIdent(queue_name)}`
    const dlqTable = `${table}_dlq`
    const now = Date.now()

    await this.tx(async (tx) => {
      // 1. Fetch message metadata
      const row = firstRow<any>(
        await tx.exec(
          `SELECT message_json, attempts FROM ${table} WHERE tenant_id=? AND id=?`,
          [tenant_id, message_id]
        )
      )

      if (!row) return

      // 2. Insert into DLQ
      await tx.exec(
        `INSERT INTO ${dlqTable} (tenant_id, id, message_json, attempts, error, failed_at)
         VALUES (?,?,?,?,?,?)`,
        [tenant_id, message_id, row.message_json, row.attempts, error, now]
      )

      // 3. Remove from main queue
      await tx.exec(
        `DELETE FROM ${table} WHERE tenant_id=? AND id=?`,
        [tenant_id, message_id]
      )
    })
  }

  async getMetrics (params: {
    tenant_id: TenantId
    queue_name: string
  }): Promise<{
    depth: number
    oldest_message_age_seconds: number | null
    dlq_size: number
  }> {
    const { tenant_id, queue_name } = params
    const table = `queue_${escapeIdent(queue_name)}`
    const dlqTable = `${table}_dlq`
    const now = nowUnix()

    return this.tx(async (tx) => {
      const depthRow = firstRow<any>(
        await tx.exec(`SELECT COUNT(*) as cnt FROM ${table} WHERE tenant_id=?`, [tenant_id])
      )
      const oldestRow = firstRow<any>(
        await tx.exec(`SELECT MIN(created_at) as min_ts FROM ${table} WHERE tenant_id=?`, [tenant_id])
      )
      const dlqRow = firstRow<any>(
        await tx.exec(`SELECT COUNT(*) as cnt FROM ${dlqTable} WHERE tenant_id=?`, [tenant_id])
      )

      const minTs = oldestRow?.min_ts ? Math.floor(oldestRow.min_ts / 1000) : null

      return {
        depth: depthRow?.cnt ?? 0,
        oldest_message_age_seconds: minTs ? now - minTs : null,
        dlq_size: dlqRow?.cnt ?? 0,
      }
    })
  }

  async listDlq (params: {
    tenant_id: TenantId
    queue_name: string
    limit?: number
  }): Promise<any[]> {
    const { tenant_id, queue_name, limit = 50 } = params
    const table = `queue_${escapeIdent(queue_name)}_dlq`
    const rows = await this.db.prepare(`SELECT * FROM ${table} WHERE tenant_id=? LIMIT ?`).bind(tenant_id, limit).all()
    return rows.results ?? []
  }

  async replayDlq (params: {
    tenant_id: TenantId
    queue_name: string
    message_id: string
  }): Promise<void> {
    const { tenant_id, queue_name, message_id } = params
    const table = `queue_${escapeIdent(queue_name)}`
    const dlqTable = `${table}_dlq`
    const now = nowUnix()

    await this.tx(async (tx) => {
      const row = firstRow<any>(
        await tx.exec(`SELECT message_json FROM ${dlqTable} WHERE tenant_id=? AND id=?`, [tenant_id, message_id])
      )
      if (!row) return

      await tx.exec(
        `INSERT INTO ${table} (tenant_id, id, message_json, attempts, visible_after, created_at, updated_at)
         VALUES (?,?,?,?,?,?,?)`,
        [tenant_id, message_id, row.message_json, 0, Date.now(), Date.now(), Date.now()]
      )
      await tx.exec(`DELETE FROM ${dlqTable} WHERE tenant_id=? AND id=?`, [tenant_id, message_id])
    })
  }

  // --------------------------
  // Schedules
  // --------------------------

  async schedule_job (params: {
    tenant_id: TenantId
    job: Omit<ScheduledJob, "id" | "status" | "attempts" | "created_at" | "updated_at">
  }): Promise<string> {
    const { tenant_id, job } = params
    const id = crypto.randomUUID()
    const now = Date.now()

    await this.tx(async (tx) => {
      await tx.exec(
        `INSERT INTO scheduled_jobs (
          tenant_id, id, schedule_name, trigger_type, entity_type, entity_id, event_type,
          scheduled_at, timezone, command_entity, command_name, input_json, queue_name,
          status, attempts, created_at, updated_at
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)`,
        [
          tenant_id, id, job.schedule_name, job.trigger_type, job.entity_type ?? null, job.entity_id ?? null, job.event_type ?? null,
          job.scheduled_at, job.timezone ?? null, job.command_entity, job.command_name, job.input_json, job.queue_name ?? null,
          "pending", 0, now, now
        ]
      )
    })
    return id
  }

  async list_due_jobs (params: {
    tenant_id: TenantId
    now: number
    limit?: number
  }): Promise<ScheduledJob[]> {
    const { tenant_id, now, limit = 10 } = params
    const rows = await this.db.prepare(
      `SELECT * FROM scheduled_jobs 
       WHERE tenant_id=? AND status IN ('pending', 'failed') AND (next_retry_at IS NULL OR next_retry_at <= ?) AND scheduled_at <= ?
       ORDER BY scheduled_at ASC
       LIMIT ?`
    ).bind(tenant_id, now, now, limit).all<ScheduledJob>()
    return rows.results ?? []
  }

  async mark_job_executing (params: {
    tenant_id: TenantId
    id: string
    now: number
  }): Promise<boolean> {
    const { tenant_id, id, now } = params
    return this.tx(async (tx) => {
      const res = await tx.exec(
        `UPDATE scheduled_jobs SET status='executing', updated_at=?, attempts=attempts+1
         WHERE tenant_id=? AND id=? AND status IN ('pending', 'failed')`,
        [now, tenant_id, id]
      )
      return ((res as any).count ?? 0) > 0
    })
  }

  async complete_job (params: {
    tenant_id: TenantId
    id: string
    now: number
  }): Promise<void> {
    const { tenant_id, id, now } = params
    await this.tx(async (tx) => {
      await tx.exec(
        `UPDATE scheduled_jobs SET status='completed', executed_at=?, updated_at=?
         WHERE tenant_id=? AND id=?`,
        [now, now, tenant_id, id]
      )
    })
  }

  async fail_job (params: {
    tenant_id: TenantId
    id: string
    error: string
    next_retry_at?: number
  }): Promise<void> {
    const { tenant_id, id, error, next_retry_at } = params
    const now = Date.now()
    await this.tx(async (tx) => {
      await tx.exec(
        `UPDATE scheduled_jobs SET status='failed', last_error=?, next_retry_at=?, updated_at=?
         WHERE tenant_id=? AND id=?`,
        [error, next_retry_at ?? null, now, tenant_id, id]
      )
    })
  }

  async cancel_job (params: {
    tenant_id: TenantId
    id: string
  }): Promise<void> {
    const { tenant_id, id } = params
    const now = Date.now()
    await this.tx(async (tx) => {
      await tx.exec(
        `UPDATE scheduled_jobs SET status='canceled', updated_at=?
         WHERE tenant_id=? AND id=?`,
        [now, tenant_id, id]
      )
    })
  }

  async get_job (params: {
    tenant_id: TenantId
    id: string
  }): Promise<ScheduledJob | null> {
    const { tenant_id, id } = params
    return await this.db.prepare(`SELECT * FROM scheduled_jobs WHERE tenant_id=? AND id=?`).bind(tenant_id, id).first<ScheduledJob>()
  }

  async list_jobs_for_entity (params: {
    tenant_id: TenantId
    entity_type: string
    entity_id: string
  }): Promise<ScheduledJob[]> {
    const { tenant_id, entity_type, entity_id } = params
    const rows = await this.db.prepare(
      `SELECT * FROM scheduled_jobs WHERE tenant_id=? AND entity_type=? AND entity_id=? ORDER BY created_at DESC`
    ).bind(tenant_id, entity_type, entity_id).all<ScheduledJob>()
    return rows.results ?? []
  }

  async get_schedule_metrics (params: {
    tenant_id: TenantId
  }): Promise<{
    pending_count: number
    failed_count: number
    avg_latency_ms: number
  }> {
    const { tenant_id } = params
    return this.tx(async (tx) => {
      const counts = await tx.exec(
        `SELECT status, COUNT(*) as cnt FROM scheduled_jobs WHERE tenant_id=? GROUP BY status`,
        [tenant_id]
      )
      const res = (counts as any).rows ?? []
      const pending = res.find((r: any) => (r as any).status === "pending")?.cnt ?? 0
      const failed = res.find((r: any) => (r as any).status === "failed")?.cnt ?? 0

      const latencyRow = firstRow<any>(
        await tx.exec(
          `SELECT AVG(executed_at - scheduled_at) as avg_latency FROM scheduled_jobs 
            WHERE tenant_id=? AND status='completed' AND executed_at IS NOT NULL`,
          [tenant_id]
        )
      )

      return {
        pending_count: Number(pending),
        failed_count: Number(failed),
        avg_latency_ms: Number(latencyRow?.avg_latency ?? 0),
      }
    })
  }

  // --------------------------
  // Cron Schedules
  // --------------------------

  async upsert_cron_schedule (params: {
    tenant_id: TenantId
    name: string
    expression: string
    timezone?: string
    next_run_at: number
  }): Promise<void> {
    const { tenant_id, name, expression, timezone, next_run_at } = params
    await this.tx(async (tx) => {
      await tx.exec(
        `INSERT INTO cron_schedules (tenant_id, name, expression, timezone, next_run_at)
         VALUES (?,?,?,?,?)
         ON CONFLICT(tenant_id, name) DO UPDATE SET 
           expression=excluded.expression, 
           timezone=excluded.timezone, 
           next_run_at=excluded.next_run_at`,
        [tenant_id, name, expression, timezone ?? null, next_run_at]
      )
    })
  }

  async list_due_cron_schedules (params: {
    tenant_id: TenantId
    now: number
  }): Promise<any[]> {
    const { tenant_id, now } = params
    const rows = await this.db.prepare(
      `SELECT * FROM cron_schedules WHERE tenant_id=? AND next_run_at <= ?`
    ).bind(tenant_id, now).all()
    return rows.results ?? []
  }

  async update_cron_last_run (params: {
    tenant_id: TenantId
    name: string
    last_run_at: number
    next_run_at: number
  }): Promise<void> {
    const { tenant_id, name, last_run_at, next_run_at } = params
    await this.tx(async (tx) => {
      await tx.exec(
        `UPDATE cron_schedules SET last_run_at=?, next_run_at=?
         WHERE tenant_id=? AND name=?`,
        [last_run_at, next_run_at, tenant_id, name]
      )
    })
  }

  // Workflows
  async create_workflow_instance (instance: any): Promise<void> {
    await this.db
      .prepare(
        `INSERT INTO workflow_instances 
        (tenant_id, workflow_id, workflow_name, current_step, status, wait_event_type, context_json, history_json, next_run_at, created_ts, updated_ts)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`
      )
      .bind(
        instance.tenant_id,
        instance.workflow_id,
        instance.workflow_name,
        instance.current_step,
        instance.status,
        instance.wait_event_type,
        instance.context_json,
        instance.history_json,
        instance.next_run_at,
        instance.created_ts,
        instance.updated_ts
      )
      .run()
  }

  async update_workflow_instance (instance: any): Promise<void> {
    const fields: string[] = []
    const params: any[] = []

    if (instance.current_step !== undefined) {
      fields.push("current_step = ?")
      params.push(instance.current_step)
    }
    if (instance.status !== undefined) {
      fields.push("status = ?")
      params.push(instance.status)
    }
    if (instance.wait_event_type !== undefined) {
      fields.push("wait_event_type = ?")
      params.push(instance.wait_event_type)
    }
    if (instance.context_json !== undefined) {
      fields.push("context_json = ?")
      params.push(instance.context_json)
    }
    if (instance.history_json !== undefined) {
      fields.push("history_json = ?")
      params.push(instance.history_json)
    }
    if (instance.next_run_at !== undefined) {
      fields.push("next_run_at = ?")
      params.push(instance.next_run_at)
    }
    if (instance.updated_ts !== undefined) {
      fields.push("updated_ts = ?")
      params.push(instance.updated_ts)
    }

    if (fields.length === 0) return

    params.push(instance.tenant_id, instance.workflow_id)
    await this.db
      .prepare(`UPDATE workflow_instances SET ${fields.join(", ")} WHERE tenant_id = ? AND workflow_id = ?`)
      .bind(...params)
      .run()
  }

  async list_workflow_instances_waiting_for_event (params: { tenant_id: string; event_type: string }): Promise<any[]> {
    const res = await this.db
      .prepare(`SELECT * FROM workflow_instances WHERE tenant_id = ? AND status = 'waiting' AND wait_event_type = ?`)
      .bind(params.tenant_id, params.event_type)
      .all()
    return res.results || []
  }

  async get_workflow_instance (tenant_id: string, workflow_id: string): Promise<any | null> {
    const res = await this.db
      .prepare(`SELECT * FROM workflow_instances WHERE tenant_id = ? AND workflow_id = ?`)
      .bind(tenant_id, workflow_id)
      .first()
    return res
  }

  async list_due_workflow_instances (params: { tenant_id: string; now: number }): Promise<any[]> {
    const res = await this.db
      .prepare(
        `SELECT * FROM workflow_instances WHERE tenant_id = ? AND (status = 'running' OR (status = 'waiting' AND next_run_at <= ?))`
      )
      .bind(params.tenant_id, params.now)
      .all()
    return res.results || []
  }

  async append_workflow_log (entry: any): Promise<void> {
    await this.db
      .prepare(`INSERT INTO workflow_log (tenant_id, workflow_id, step_name, action, payload_json, ts) VALUES (?, ?, ?, ?, ?, ?)`)
      .bind(entry.tenant_id, entry.workflow_id, entry.step_name, entry.action, entry.payload_json, entry.ts)
      .run()
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
