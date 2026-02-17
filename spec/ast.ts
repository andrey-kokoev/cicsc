export type SpecV0 = {
  version: 0
  entities: Record<string, SpecEntityV0>
  policies?: Record<string, SpecPolicyV0>
  constraints?: Record<string, SpecConstraintV0>
  views?: Record<string, SpecViewV0>
  slas?: Record<string, SpecSlaV0>
  schedules?: Record<string, SpecScheduleV0>
  workflows?: Record<string, SpecWorkflowV0>
  multi_entity_commands?: Record<string, SpecMultiEntityCommandV0>
  ui?: Record<string, SpecUiV0>
  migrations?: Record<string, SpecMigrationV0>
  subscriptions?: Record<string, SpecSubscriptionV0>
  webhooks?: Record<string, SpecWebhookV0>
  queues?: Record<string, SpecQueueV0>
}

export type SpecEntityV0 = {
  id: "string"
  states: string[]
  initial: string

  attributes?: Record<string, SpecAttrV0>
  shadows?: Record<string, SpecShadowV0>

  commands?: Record<string, SpecCommandV0>
  reducers?: Record<string, any[]>
}

export type SpecAttrV0 = {
  type: "string" | "int" | "float" | "bool" | "time" | "enum"
  optional?: boolean
  values?: string[]
}

export type SpecShadowV0 = {
  type: "string" | "int" | "float" | "bool" | "time" | "enum"
}

export type SpecCommandV0 = {
  inputs?: Record<string, SpecAttrV0>
  when?: any
  auth?: { cmdref?: string; policy?: string }
  emit: Array<{ type: string; payload?: Record<string, any> }>
}

export type SpecConstraintV0 =
  | { kind: "snapshot"; entity: string; when: any }
  | { kind: "bool_query"; entity: string; args?: Record<string, SpecAttrV0>; query: any; assert: any }

export type SpecViewV0 = {
  kind: string
  on: string
  query?: any
  row_policy?: any
  lanes?: {
    states?: string[]
    order_by?: { field: string; dir?: "asc" | "desc" }
    limit?: number
  }
  [k: string]: any
}

export type SpecPolicyV0 = {
  params?: string[]
  allow?: any
}

export type SpecSlaV0 = {
  on: string
  start_event: string
  start_occurrence?: "first"
  start_where?: any
  stop_event: string
  stop_occurrence?: "first"
  stop_where?: any
  within_seconds: number
  enforce?: "none" | { notify: { emit_event: string; payload?: Record<string, any> } } | { auto_transition: { to_state: string } }
}

export type SpecScheduleV0 = {
  trigger_cron?: {
    expression: string
    timezone?: string
  }
  trigger_delay?: {
    seconds: number
  }
  trigger_event?: {
    on_type: string
    event_type: string
    where?: any
  }
  action_target_command?: {
    entity_type: string
    entity_id_expr?: any
    command_name: string
  }
  action_target_webhook?: {
    url: string
    method?: string
  }
  action_target_queue?: {
    name: string
  }
  action_input_map?: Record<string, any>
  action_retry_policy?: SpecRetryPolicyV0
  enabled?: boolean
  metadata?: Record<string, string>
}

export type SpecWorkflowV0 = {
  start_step: string
  steps: Record<string, SpecWorkflowStepV0>
  compensation?: SpecWorkflowCompensationV0
  metadata?: Record<string, string>
}

export type SpecWorkflowStepV0 =
  | { command: SpecWorkflowCommandStepV0 }
  | { wait: SpecWorkflowWaitStepV0 }
  | { decision: SpecWorkflowDecisionStepV0 }
  | { parallel: SpecWorkflowParallelStepV0 }

export type SpecWorkflowCommandStepV0 = {
  target_command?: {
    entity_type: string
    entity_id_expr?: any
    command_name: string
  }
  target_webhook?: {
    url: string
    method?: string
  }
  target_queue?: {
    name: string
  }
  input_map?: Record<string, any>
  on_success?: string
  on_failure?: string
  retry_policy?: SpecRetryPolicyV0
}

export type SpecWorkflowWaitStepV0 = {
  timeout_seconds?: number
  wait_for_event?: {
    on_type: string
    event_type: string
    where?: any
  }
  on_timeout?: string
  on_event?: string
}

export type SpecWorkflowDecisionStepV0 = {
  condition: any
  on_true: string
  on_false: string
}

export type SpecWorkflowParallelStepV0 = {
  branches: Record<string, SpecWorkflowStepV0>
  on_completion: string
  on_failure?: string
}

export type SpecWorkflowCompensationV0 = {
  strategy: "saga" | "reverse-order" | "custom"
  custom_steps?: Record<string, SpecWorkflowStepV0>
}

export type SpecRetryPolicyV0 = {
  max_attempts: number
  backoff: {
    initial_delay_ms: number
    max_delay_ms: number
    multiplier: number
  }
}

export type SpecMultiEntityCommandV0 = {
  steps: Array<SpecMultiEntityCommandStepV0>
  transaction_boundary: {
    kind: "atomic" | "compensatable" | "best_effort"
    isolation_level?: "read_uncommitted" | "read_committed" | "repeatable_read" | "serializable"
  }
  compensation_strategy?: {
    strategy: "saga" | "rollback" | "manual"
    saga_steps?: Array<SpecCompensationStepV0>
  }
  partial_failure_handling: {
    strategy: "fail_fast" | "continue_and_compensate" | "partial_commit"
    on_failure?: "compensate_all" | "compensate_partial" | "manual_intervention"
  }
}

export type SpecMultiEntityCommandStepV0 =
  | { command: {
      entity_type: string
      entity_id_expr: any
      command_name: string
      input: Record<string, any>
    }}
  | { wait: { duration_ms: number } }
  | { condition: {
      expr: any
      then_steps: SpecMultiEntityCommandStepV0[]
      else_steps?: SpecMultiEntityCommandStepV0[]
    }}

export type SpecCompensationStepV0 = {
  entity_type: string
  entity_id_expr: any
  command_name: string
  input: Record<string, any>
}

export type SpecUiV0 = {
  screens?: Record<string, SpecScreenV0>
  dashboards?: Record<string, SpecDashboardV0>
  navigation?: SpecNavigationV0
  themes?: Record<string, SpecThemeV0>
}

export type SpecScreenV0 = {
  title: string
  description?: string
  layout: SpecLayoutV0
  data_source: SpecDataSourceV0
  permissions?: SpecPermissionV0
}

export type SpecDashboardV0 = {
  title: string
  description?: string
  widgets: SpecWidgetV0[]
  layout: SpecLayoutV0
  permissions?: SpecPermissionV0
}

export type SpecNavigationV0 = {
  sections: SpecNavigationSectionV0[]
}

export type SpecNavigationSectionV0 = {
  id: string
  title: string
  icon?: string
  items: SpecNavigationItemV0[]
  permissions?: SpecPermissionV0
}

export type SpecNavigationItemV0 = {
  id: string
  title: string
  route: string
  icon?: string
  permissions?: SpecPermissionV0
}

export type SpecLayoutV0 =
  | { grid: { columns: number; items: SpecLayoutItemV0[] } }
  | { form: { fields: SpecFormFieldV0[] } }
  | { table: { columns: SpecTableColumnV0[] } }
  | { tabs: { tabs: SpecTabV0[] } }
  | { sidebar: { main: SpecLayoutV0; sidebar: SpecLayoutV0 } }

export type SpecLayoutItemV0 = {
  component: string
  props: Record<string, any>
  col_span?: number
  row_span?: number
}

export type SpecFormFieldV0 = {
  name: string
  label: string
  type: "text" | "number" | "boolean" | "date" | "select" | "textarea" | "file"
  required?: boolean
  validation?: any
  default_value?: any
}

export type SpecTableColumnV0 = {
  name: string
  label: string
  type: "text" | "number" | "boolean" | "date" | "link" | "action"
  sortable?: boolean
  filterable?: boolean
  formatter?: any
}

export type SpecTabV0 = {
  id: string
  title: string
  content: SpecLayoutV0
}

export type SpecWidgetV0 = {
  id: string
  title: string
  type: "metric" | "chart" | "table" | "list" | "form"
  data_source: SpecDataSourceV0
  config: Record<string, any>
}

export type SpecDataSourceV0 =
  | { view: { view_name: string; args?: Record<string, any> } }
  | { entity: { entity_type: string; query?: any } }
  | { api: { endpoint: string; method?: string; params?: Record<string, any> } }

export type SpecPermissionV0 = {
  roles?: string[]
  conditions?: any[]
}

export type SpecThemeV0 = {
  name: string
  mode: "light" | "dark" | "auto"
  colors: Record<string, string>
  spacing: Record<string, number>
  typography: SpecTypographyV0
}

export type SpecTypographyV0 = {
  font_family?: string
  sizes: Record<string, number>
  weights: Record<string, number>
}

export type SpecMigrationV0 = {
  from: number
  to: number
  entity: string
  event_transforms: Record<string, SpecEventTransformV0>
  state_map?: Record<string, string>
}

export type SpecEventTransformV0 = {
  emit_as?: string
  payload_map?: Record<string, any>
  drop?: boolean
  fan_out?: SpecFanOutTransformV0
}

export type SpecFanOutTransformV0 = {
  emit_many: Array<{
    emit_as: string
    payload_map?: Record<string, any>
    condition?: any  // Expression to determine if this event should be emitted
  }>
}

export type SpecSubscriptionV0 = {
  on: string
  filter?: any
}

export type SpecWebhookV0 = {
  on: string
  command: string
  queue?: string
  payload_map?: Record<string, any>
  verify?: {
    hmac?: {
      secret_env: string
      header: string
      algo: "sha256"
    }
  }
}

export type SpecQueueV0 = {
  message_type: Record<string, SpecAttrV0>
  ordering?: "unordered" | "fifo" | "per_key"
  retention?: {
    max_age_seconds: number
    max_depth?: number
  }
  delivery?: {
    max_attempts: number
    initial_backoff_ms: number
    max_backoff_ms: number
    dead_letter_queue?: string
  }
  map_to?: {
    command: string // format: Entity.Command
    input_map: Record<string, any>
  }
}
