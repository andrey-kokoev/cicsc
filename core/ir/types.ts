// /core/ir/types.ts

export type CoreIrBundleV0 = {
  core_ir: CoreIrV0
}

export type CoreIrV0 = {
  version: 0
  types: Record<string, EntityTypeSpecV0>
  policies?: Record<string, PolicySpecV0>
  constraints?: Record<string, ConstraintSpecV0>
  views?: Record<string, ViewSpecV0>
  slas?: Record<string, SlaSpecV0>
  migrations?: Record<string, MigrationSpecV0>
  subscriptions?: Record<string, SubscriptionSpecV0>
  webhooks?: Record<string, WebhookSpecV0>
  queues?: Record<string, QueueSpecV0>
}

export type EntityTypeSpecV0 = {
  id_type: string // "string"
  states: string[]
  initial_state: string

  attrs: Record<string, AttrTypeSpecV0>
  shadows?: Record<string, ShadowTypeSpecV0>

  commands: Record<string, CommandSpecV0>
  reducer: Record<string, ReducerOpV0[]> // keyed by event_type
}

export type AttrTypeSpecV0 = {
  type?: string // "string" | "int" | "float" | "bool" | "time" | "enum" | "json"
  optional?: boolean
  default?: unknown
  values?: string[] // for enum
}

export type ShadowTypeSpecV0 = {
  type?: string // "string" | "int" | "float" | "bool" | "time"
  expr?: ExprV0 // optional: compiler may precompute
}

export type CommandSpecV0 = {
  input: Record<string, AttrTypeSpecV0>
  guard: { expr: ExprV0 }
  emits: { event_type: string; payload: Record<string, ExprV0> }[]
}

export type PolicySpecV0 = {
  params: string[]
  expr: ExprV0
}

export type ConstraintSpecV0 =
  | SnapshotConstraintV0
  | BoolQueryConstraintV0

export type SnapshotConstraintV0 = {
  kind: "snapshot"
  on_type: string
  expr: ExprV0
}

export type BoolQueryConstraintV0 = {
  kind: "bool_query"
  on_type: string
  args: Record<string, AttrTypeSpecV0>
  query: QueryV0
  assert: ExprV0 // evaluated in assert env
}

export type ViewSpecV0 = {
  kind: "lanes" | "metric"
  on_type?: string
  lanes?: string[]
  args?: Record<string, AttrTypeSpecV0>
  row_policy?: ExprV0
  query: QueryV0
}

export type SlaSpecV0 = {
  name: string
  on_type: string
  start: { event: EventSelectorV0 }
  stop: { event: EventSelectorV0 }
  within_seconds: number
  enforce:
  | { none: true }
  | { notify: { emit_event: string; payload: Record<string, ExprV0> } }
  | { auto_transition: { to_state: string } }
}

export type MigrationSpecV0 = {
  from_version: number
  to_version: number
  on_type: string
  event_transforms: Record<string, EventTransformV0>
  state_map?: Record<string, string>
}

export type SubscriptionSpecV0 = {
  on_type: string
  filter?: ExprV0
}

export type WebhookSpecV0 = {
  on_type: string
  command: string
  queue?: string
  routing?: ExprV0
  verify?: {
    hmac?: {
      secret_env: string
      header: string
      algo: "sha256"
    }
  }
}

export type QueueSpecV0 = {
  message_type: Record<string, AttrTypeSpecV0>
  ordering?: "unordered" | "fifo" | "per_key"
  retention: {
    max_age_seconds: number
    max_depth?: number
  }
  delivery: {
    max_attempts: number
    initial_backoff_ms: number
    max_backoff_ms: number
    dead_letter_queue?: string
  }
  map_to?: QueueCommandMappingV0
}

export type QueueCommandMappingV0 = {
  entity_type: string
  command: string
  input_map: Record<string, ExprV0>
}

export type EventTransformV0 = {
  emit_as?: string
  payload_map?: Record<string, ExprV0>
  drop?: boolean
}

export type EventSelectorV0 = {
  name: string // event_type
  occurrence?: "first"
  where?: ExprV0 // restricted env
}

export type ReducerOpV0 =
  | { set_state: { expr: ExprV0 } }
  | { set_attr: { name: string; expr: ExprV0 } }
  | { clear_attr: { name: string } }
  | { set_shadow: { name: string; expr: ExprV0 } }

// ---------------------------
// Expr AST v0 (closed)
// ---------------------------

export type ExprV0 =
  | { lit: LiteralV0 }
  | { var: VarRefV0 }
  | { get: { expr: ExprV0; path: string } }
  | { has: { expr: ExprV0; path: string } }
  | { obj: { fields: Record<string, ExprV0> } }
  | { arr: { items: ExprV0[] } }

  | { not: ExprV0 }
  | { and: ExprV0[] }
  | { or: ExprV0[] }
  | { bool: ExprV0 }

  | { eq: [ExprV0, ExprV0] }
  | { ne: [ExprV0, ExprV0] }
  | { lt: [ExprV0, ExprV0] }
  | { le: [ExprV0, ExprV0] }
  | { gt: [ExprV0, ExprV0] }
  | { ge: [ExprV0, ExprV0] }
  | { in: { needle: ExprV0; haystack: ExprV0 } }

  | { add: [ExprV0, ExprV0] }
  | { sub: [ExprV0, ExprV0] }
  | { mul: [ExprV0, ExprV0] }
  | { div: [ExprV0, ExprV0] }

  | { if: { cond: ExprV0; then: ExprV0; else: ExprV0 } }
  | { coalesce: ExprV0[] }
  | { is_null: ExprV0 }

  | { time_between: [ExprV0, ExprV0] }
  | { map_enum: { expr: ExprV0; mapping: Record<string, number> } }

  | { call: { fn: IntrinsicFnV0; args: ExprV0[] } }

export type LiteralV0 =
  | { null: true }
  | { bool: boolean }
  | { int: number }
  | { float: number }
  | { string: string }

export type VarRefV0 =
  | { now: true }
  | { actor: true }
  | { state: true }
  | { input: { field: string } }
  | { attrs: { field: string } }
  | { row: { field: string } }
  | { arg: { name: string } }
  | { rows_count: true }
  | { agg: { name: string } }
  | { e_type: true }
  | { e_actor: true }
  | { e_time: true }
  | { e_payload: { path: string } }
  | { payload: { path: string } }

export type IntrinsicFnV0 =
  | "has_role"
  | "role_of"
  | "auth_ok"
  | "allowed"
  | "constraint"
  | "len"
  | "str"
  | "int"
  | "float"

// ---------------------------
// Query AST v0
// ---------------------------

export type QueryV0 = {
  source: SourceV0
  pipeline: OpV0[]
}

export type SourceV0 =
  | { snap: { type: string } }
  | { sla_status: { name: string; on_type: string } }
  | { join: { left: SourceV0; right: SourceV0; on: JoinOnV0 } }

export type JoinOnV0 = { left_field: string; right_field: string }

export type OpV0 =
  | { filter: ExprV0 }
  | { project: { fields: FieldRefV0[] } }
  | { group_by: { keys: FieldRefV0[]; aggs: Record<string, AggExprV0> } }
  | { order_by: OrderKeyV0[] }
  | { limit: number }
  | { offset: number }

export type FieldRefV0 = { name: string; expr: ExprV0 }
export type OrderKeyV0 = { expr: ExprV0; dir: "asc" | "desc" }

export type AggExprV0 =
  | { count: { expr?: { value: ExprV0 } } }
  | { sum: { expr: ExprV0 } }
  | { min: { expr: ExprV0 } }
  | { max: { expr: ExprV0 } }
  | { rate: { numerator: ExprV0; denominator: ExprV0; unit: "per_second" | "per_minute" | "per_hour" | "per_day" } }
  | { ratio: { numerator: ExprV0; denominator: ExprV0; scale?: number } }
  | { time_between: { start_expr: ExprV0; end_expr: ExprV0; unit?: "seconds" | "minutes" | "hours" | "days" } }
