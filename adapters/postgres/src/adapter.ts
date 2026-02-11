// /adapters/postgres/src/adapter.ts

import type { Pool, PoolClient } from "pg"
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

export class PostgresAdapter {
  readonly caps: Capabilities = {
    transactions: { atomic_batch_append: true, snapshot_in_same_tx: true },
    query: { joins: true, secondary_indexes: "full", json_extract: "full" },
    constraints: { snapshot_vm: true, bool_query: true },
    projections: { query_time: true, materialized: true },
    scheduler: { cron: false }, // assume external scheduler
  };

  constructor(private readonly pool: Pool) { }

  async with_txn<T> (fn: (c: PoolClient) => Promise<T>): Promise<T> {
    const c = await this.pool.connect()
    try {
      await c.query("BEGIN")
      const out = await fn(c)
      await c.query("COMMIT")
      return out
    } catch (e) {
      await c.query("ROLLBACK")
      throw e
    } finally {
      c.release()
    }
  }

  async get_active_version (c: PoolClient, tenant_id: TenantId): Promise<number> {
    const r = await c.query<{ active_version: number }>(
      `SELECT active_version FROM tenant_versions WHERE tenant_id=$1`,
      [tenant_id]
    )
    return r.rowCount ? r.rows[0]!.active_version : 0
  }

  async set_active_version (tenant_id: TenantId, version: number): Promise<void> {
    await this.pool.query(
      `INSERT INTO tenant_versions(tenant_id, active_version) VALUES($1,$2)
       ON CONFLICT(tenant_id) DO UPDATE SET active_version=excluded.active_version`,
      [tenant_id, version]
    )
  }

  async append_events (params: {
    tenant_id: TenantId
    entity_type: EntityType
    entity_id: EntityId
    command_id: CommandId
    events: EventRecord[]
  }): Promise<AppendResult> {
    const { tenant_id, entity_type, entity_id, command_id, events } = params
    if (!events.length) throw new Error("append_events: empty batch")

    return this.with_txn(async (c) => {
      // idempotency
      const rec = await c.query<{ result_json: any }>(
        `SELECT result_json FROM command_receipts WHERE tenant_id=$1 AND command_id=$2`,
        [tenant_id, command_id]
      )
      if (rec.rowCount) return rec.rows[0]!.result_json as AppendResult

      const ver = await this.get_active_version(c, tenant_id)
      const eventsTable = `events_v${ver}`
      const snapshotsTable = `snapshots_v${ver}`

      // lock stream and compute next seq
      const max = await c.query<{ max_seq: string }>(
        `SELECT COALESCE(MAX(seq),0)::text AS max_seq
         FROM ${eventsTable}
         WHERE tenant_id=$1 AND entity_type=$2 AND entity_id=$3
         FOR UPDATE`,
        [tenant_id, entity_type, entity_id]
      )
      const seqStart = BigInt(max.rows[0]!.max_seq) + 1n

      for (let i = 0; i < events.length; i++) {
        const e = events[i]!
        const seq = seqStart + BigInt(i)
        await c.query(
          `INSERT INTO ${eventsTable}
           (tenant_id, entity_type, entity_id, seq, event_type, payload, ts, actor_id)
           VALUES($1,$2,$3,$4,$5,$6,$7,$8)`,
          [tenant_id, entity_type, entity_id, seq.toString(), e.event_type, e.payload ?? null, e.ts, e.actor_id]
        )
      }

      // ensure snapshot exists
      await c.query(
        `INSERT INTO ${snapshotsTable}(tenant_id, entity_type, entity_id, state, attrs, updated_ts)
         VALUES($1,$2,$3,$4,$5,$6)
         ON CONFLICT(tenant_id, entity_type, entity_id) DO NOTHING`,
        [tenant_id, entity_type, entity_id, "new", {}, nowUnix()]
      )

      const result: AppendResult = {
        entity_id,
        seq_from: Number(seqStart),
        seq_to: Number(seqStart + BigInt(events.length - 1)),
      }

      await c.query(
        `INSERT INTO command_receipts(tenant_id, command_id, entity_type, entity_id, result_json, ts)
         VALUES($1,$2,$3,$4,$5,$6)
         ON CONFLICT(tenant_id, command_id) DO NOTHING`,
        [tenant_id, command_id, entity_type, entity_id, result, nowUnix()]
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
    const lim = Math.max(1, Math.min(limit ?? 500, 2000))
    const fromSeq = from?.seq ?? 0

    const c = await this.pool.connect()
    try {
      const ver = await this.get_active_version(c, tenant_id)
      const eventsTable = `events_v${ver}`
      const r = await c.query<EventRow>(
        `SELECT tenant_id, entity_type, entity_id, seq::int, event_type, payload, ts::int, actor_id
         FROM ${eventsTable}
         WHERE tenant_id=$1 AND entity_type=$2 AND entity_id=$3 AND seq>$4
         ORDER BY seq ASC
         LIMIT $5`,
        [tenant_id, entity_type, entity_id, fromSeq, lim]
      )
      const next = r.rowCount === lim ? { seq: r.rows[r.rows.length - 1]!.seq } : undefined
      return { events: r.rows, next }
    } finally {
      c.release()
    }
  }

  async get_snapshot (params: {
    tenant_id: TenantId
    entity_type: EntityType
    entity_id: EntityId
  }): Promise<SnapshotRow | null> {
    const { tenant_id, entity_type, entity_id } = params
    const c = await this.pool.connect()
    try {
      const ver = await this.get_active_version(c, tenant_id)
      const snapshotsTable = `snapshots_v${ver}`
      const r = await c.query<SnapshotRow>(
        `SELECT tenant_id, entity_type, entity_id, state, attrs, updated_ts::int AS updated_ts
         FROM ${snapshotsTable}
         WHERE tenant_id=$1 AND entity_type=$2 AND entity_id=$3`,
        [tenant_id, entity_type, entity_id]
      )
      return r.rowCount ? r.rows[0]! : null
    } finally {
      c.release()
    }
  }

  async put_snapshot (params: {
    tenant_id: TenantId
    entity_type: EntityType
    entity_id: EntityId
    state: string
    attrs: unknown
    updated_ts: UnixSeconds
    shadows?: Record<string, string | number | null>
  }): Promise<void> {
    const { tenant_id, entity_type, entity_id, state, attrs, updated_ts, shadows } = params
    await this.with_txn(async (c) => {
      const ver = await this.get_active_version(c, tenant_id)
      const snapshotsTable = `snapshots_v${ver}`

      const shadowCols = shadows ? Object.keys(shadows) : []
      const setShadowSql =
        shadowCols.length === 0 ? "" : ", " + shadowCols.map((k, i) => `${escapeIdent(k)}=$${6 + i}`).join(", ")
      const bindShadowVals = shadowCols.map((k) => (shadows as any)[k])

      const sql =
        `UPDATE ${snapshotsTable}
         SET state=$4, attrs=$5, updated_ts=$6` +
        setShadowSql +
        ` WHERE tenant_id=$1 AND entity_type=$2 AND entity_id=$3`

      const binds = [tenant_id, entity_type, entity_id, state, attrs, updated_ts, ...bindShadowVals]
      await c.query(sql, binds)
    })
  }

  async eval_constraint_sql (params: {
    sql: string // MUST be adapter-generated
    binds: any[]
    ctx: ConstraintCtx
  }): Promise<boolean> {
    const r = await this.pool.query<{ ok: boolean }>(params.sql, params.binds)
    if (!r.rowCount) throw new Error("eval_constraint_sql: no rows")
    return !!r.rows[0]!.ok
  }

  async exec_view_sql (params: { sql: string; binds: any[] }): Promise<ViewResultPage> {
    const r = await this.pool.query<any>(params.sql, params.binds)
    return { rows: r.rows }
  }

  async sla_check_due (params: { tenant_id: TenantId; name: string; now: UnixSeconds; limit: number }): Promise<SlaBreach[]> {
    const lim = Math.max(1, Math.min(params.limit, 1000))
    const r = await this.pool.query<SlaBreach>(
      `SELECT tenant_id, name, entity_type, entity_id, deadline_ts::int AS deadline_ts
       FROM sla_status
       WHERE tenant_id=$1 AND name=$2 AND breached=false AND stop_ts IS NULL AND deadline_ts IS NOT NULL AND deadline_ts < $3
       ORDER BY deadline_ts ASC
       LIMIT $4`,
      [params.tenant_id, params.name, params.now, lim]
    )
    return r.rows
  }

  async sla_mark_breached (params: {
    tenant_id: TenantId
    name: string
    entity_type: EntityType
    entity_id: EntityId
    now: UnixSeconds
  }): Promise<void> {
    await this.pool.query(
      `UPDATE sla_status
       SET breached=true, updated_ts=$1
       WHERE tenant_id=$2 AND name=$3 AND entity_type=$4 AND entity_id=$5`,
      [params.now, params.tenant_id, params.name, params.entity_type, params.entity_id]
    )
  }
}

function nowUnix (): UnixSeconds {
  return Math.floor(Date.now() / 1000)
}

function escapeIdent (name: string): string {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new Error(`Invalid identifier: ${name}`)
  return `"${name}"`
}
