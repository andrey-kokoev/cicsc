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
  schedules?: Record<string, ScheduleSpecV0>
  workflows?: Record<string, WorkflowSpecV0>
  multi_entity_commands?: Record<string, MultiEntityCommandSpecV0>
  ui?: Record<string, UiSpecV0>
  services?: Record<string, ServiceSpecV0>
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
  target_state?: string
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

export type ScheduleSpecV0 = {
  name: string
  trigger: ScheduleTriggerV0
  action: ScheduleActionV0
  enabled?: boolean
  metadata?: Record<string, string>
}

export type ScheduleTriggerV0 =
  | { cron: { expression: string; timezone?: string } }
  | { delay: { seconds: number } }
  | { event: { on_type: string; event_type: string; where?: ExprV0 } }

export type ScheduleActionV0 = {
  target: ScheduleTargetV0
  input_map?: Record<string, ExprV0>
  retry_policy?: RetryPolicyV0
}

export type ScheduleTargetV0 =
  | { command: { entity_type: string; entity_id_expr: ExprV0; command_name: string } }
  | { webhook: { url: string; method?: string } }
  | { queue: { name: string } }

export type RetryPolicyV0 = {
  max_attempts: number
  backoff: {
    initial_delay_ms: number
    max_delay_ms: number
    multiplier: number
  }
}

export type WorkflowSpecV0 = {
  name: string
  steps: Record<string, WorkflowStepV0>
  start_step: string
  compensation?: WorkflowCompensationV0
  metadata?: Record<string, string>
}

export type WorkflowStepV0 =
  | { command: WorkflowCommandStepV0 }
  | { wait: WorkflowWaitStepV0 }
  | { decision: WorkflowDecisionStepV0 }
  | { parallel: WorkflowParallelStepV0 }

export type WorkflowCommandStepV0 = {
  target: ScheduleTargetV0  // Reusing the target concept
  input_map?: Record<string, ExprV0>
  on_success?: string  // Next step name
  on_failure?: string  // Next step name for failure handling
  retry_policy?: RetryPolicyV0
}

export type WorkflowWaitStepV0 = {
  timeout_seconds?: number
  wait_for_event?: { on_type: string; event_type: string; where?: ExprV0 }
  on_timeout?: string
  on_event?: string
}

export type WorkflowDecisionStepV0 = {
  condition: ExprV0
  on_true: string
  on_false: string
}

export type WorkflowParallelStepV0 = {
  branches: Record<string, WorkflowStepV0>
  on_completion: string
  on_failure?: string
}

export type WorkflowCompensationV0 = {
  strategy: "saga" | "reverse-order" | "custom"
  custom_steps?: Record<string, WorkflowStepV0>
}

export type MultiEntityCommandSpecV0 = {
  name: string
  steps: Array<MultiEntityCommandStepV0>
  transaction_boundary: TransactionBoundaryV0
  compensation_strategy?: CompensationStrategyV0
  partial_failure_handling: PartialFailureHandlingV0
}

export type MultiEntityCommandStepV0 =
  | { command: { entity_type: string; entity_id_expr: ExprV0; command_name: string; input: Record<string, ExprV0> } }
  | { wait: { duration_ms: number } }
  | { condition: { expr: ExprV0; then_steps: MultiEntityCommandStepV0[]; else_steps?: MultiEntityCommandStepV0[] } }

export type TransactionBoundaryV0 = {
  kind: "atomic" | "compensatable" | "best_effort"
  isolation_level?: "read_uncommitted" | "read_committed" | "repeatable_read" | "serializable"
}

export type CompensationStrategyV0 = {
  strategy: "saga" | "rollback" | "manual"
  saga_steps?: Array<CompensationStepV0>
}

export type PartialFailureHandlingV0 = {
  strategy: "fail_fast" | "continue_and_compensate" | "partial_commit"
  on_failure?: "compensate_all" | "compensate_partial" | "manual_intervention"
}

export type CompensationStepV0 = {
  entity_type: string
  entity_id_expr: ExprV0
  command_name: string
  input: Record<string, ExprV0>
}

export type UiSpecV0 = {
  screens?: Record<string, ScreenSpecV0>
  dashboards?: Record<string, DashboardSpecV0>
  navigation?: NavigationSpecV0
  themes?: Record<string, ThemeSpecV0>
}

export type ScreenSpecV0 = {
  title: string
  description?: string
  layout: LayoutSpecV0
  data_source: DataSourceSpecV0
  permissions?: PermissionSpecV0
}

export type DashboardSpecV0 = {
  title: string
  description?: string
  widgets: WidgetSpecV0[]
  layout: LayoutSpecV0
  permissions?: PermissionSpecV0
}

export type NavigationSpecV0 = {
  sections: NavigationSectionV0[]
}

export type NavigationSectionV0 = {
  id: string
  title: string
  icon?: string
  items: NavigationItemV0[]
  permissions?: PermissionSpecV0
}

export type NavigationItemV0 = {
  id: string
  title: string
  route: string
  icon?: string
  permissions?: PermissionSpecV0
}

export type LayoutSpecV0 =
  | { kind: "grid"; columns: number; items: LayoutItemV0[] }
  | { kind: "form"; fields: FormFieldV0[] }
  | { kind: "table"; columns: TableColumnV0[] }
  | { kind: "tabs"; tabs: TabSpecV0[] }
  | { kind: "sidebar"; main: LayoutSpecV0; sidebar: LayoutSpecV0 }

export type LayoutItemV0 = {
  component: string
  props: Record<string, ExprV0>
  col_span?: number
  row_span?: number
}

export type FormFieldV0 = {
  name: string
  label: string
  type: "text" | "number" | "boolean" | "date" | "select" | "textarea" | "file"
  required?: boolean
  validation?: ExprV0
  default_value?: ExprV0
}

export type TableColumnV0 = {
  name: string
  label: string
  type: "text" | "number" | "boolean" | "date" | "link" | "action"
  sortable?: boolean
  filterable?: boolean
  formatter?: ExprV0
}

export type TabSpecV0 = {
  id: string
  title: string
  content: LayoutSpecV0
}

export type WidgetSpecV0 = {
  id: string
  title: string
  type: "metric" | "chart" | "table" | "list" | "form"
  data_source: DataSourceSpecV0
  config: Record<string, ExprV0>
}

export type DataSourceSpecV0 =
  | { kind: "view"; view_name: string; args?: Record<string, ExprV0> }
  | { kind: "entity"; entity_type: string; query?: ExprV0 }
  | { kind: "api"; endpoint: string; method?: string; params?: Record<string, ExprV0> }

export type PermissionSpecV0 = {
  roles?: string[]
  conditions?: ExprV0[]
}

export type ThemeSpecV0 = {
  name: string
  mode: "light" | "dark" | "auto"
  colors: Record<string, string>
  spacing: Record<string, number>
  typography: TypographySpecV0
}

export type TypographySpecV0 = {
  font_family?: string
  sizes: Record<string, number> // h1, h2, body, etc.
  weights: Record<string, number> // normal, bold, etc.
}

export type ServiceSpecV0 = {
  name: string
  base_url: string
  auth?: ServiceAuthV0
  operations: Record<string, OperationSpecV0>
  retry_policy?: RetryPolicyV0
  circuit_breaker?: CircuitBreakerV0
  timeout_ms?: number
}

export type ServiceAuthV0 =
  | { api_key: { header: string; env_var: string } }
  | { basic: { username_env: string; password_env: string } }
  | { bearer: { token_env: string } }
  | { oauth2: { client_id_env: string; client_secret_env: string; token_url: string } }

export type OperationSpecV0 = {
  method: "GET" | "POST" | "PUT" | "DELETE" | "PATCH"
  path: string
  request_format?: RequestFormatV0
  response_format?: ResponseFormatV0
  sync?: boolean  // Whether this is a synchronous call (waits for response)
  async_return_address?: boolean  // Whether to provide a return address for async callbacks
  timeout_ms?: number
  retry_policy?: RetryPolicyV0
}

export type RequestFormatV0 = {
  content_type: "application/json" | "application/x-www-form-urlencoded" | "multipart/form-data" | string
  body_mapping?: Record<string, ExprV0>  // Maps input fields to request body
  query_params?: Record<string, ExprV0>  // Maps input fields to query parameters
  headers?: Record<string, ExprV0>       // Maps input fields to headers
}

export type ResponseFormatV0 = {
  success_codes?: number[]  // HTTP status codes that indicate success
  body_mapping?: Record<string, ExprV0>  // Maps response fields to output
  error_mapping?: Record<string, ExprV0> // Maps error response fields to error output
}

export type RetryPolicyV0 = {
  max_attempts: number
  backoff: {
    initial_delay_ms: number
    max_delay_ms: number
    multiplier: number
  }
  retry_on?: ("timeout" | "network_error" | "http_5xx" | "http_429")[]
}

export type CircuitBreakerV0 = {
  failure_threshold: number  // Number of failures before opening circuit
  timeout_ms: number         // Time to wait before attempting to close circuit
  success_threshold: number  // Number of successes to close circuit after timeout
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
  fan_out?: FanOutTransformV0
}

export type FanOutTransformV0 = {
  emit_many: Array<{
    emit_as: string
    payload_map?: Record<string, ExprV0>
    condition?: ExprV0  // Optional condition to determine if this event should be emitted
  }>
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

  | { state_will_be: string }
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
