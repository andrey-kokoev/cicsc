// /adapters/postgres/src/types.ts

export type TenantId = string
export type EntityType = string
export type EntityId = string
export type CommandId = string
export type UnixSeconds = number

export type Capabilities = {
  transactions: { atomic_batch_append: boolean; snapshot_in_same_tx: boolean }
  query: { joins: boolean; secondary_indexes: "none" | "limited" | "full"; json_extract: "none" | "limited" | "full" }
  constraints: { snapshot_vm: boolean; bool_query: boolean }
  projections: { query_time: boolean; materialized: boolean }
  scheduler: { cron: boolean }
}

export type EventRecord = {
  event_type: string
  payload: unknown
  ts: UnixSeconds
  actor_id: string
}

export type AppendResult = { entity_id: EntityId; seq_from: number; seq_to: number }

export type StreamCursor = { seq: number }

export type EventRow = {
  tenant_id: TenantId
  entity_type: EntityType
  entity_id: EntityId
  seq: number
  event_type: string
  payload: unknown
  ts: UnixSeconds
  actor_id: string
}

export type SnapshotRow = {
  tenant_id: TenantId
  entity_type: EntityType
  entity_id: EntityId
  state: string
  attrs: unknown
  updated_ts: UnixSeconds
}

export type ConstraintCtx = { now: UnixSeconds; actor_id: string; entity_type: EntityType; entity_id: EntityId }

export type ViewResultPage = { rows: unknown[]; next_cursor?: string }

export type SlaBreach = { tenant_id: TenantId; name: string; entity_type: EntityType; entity_id: EntityId; deadline_ts: UnixSeconds }
