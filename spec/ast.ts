export type SpecV0 = {
  version: 0
  entities: Record<string, SpecEntityV0>
  policies?: Record<string, SpecPolicyV0>
  constraints?: Record<string, SpecConstraintV0>
  views?: Record<string, SpecViewV0>
  slas?: Record<string, SpecSlaV0>
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
  // Rich aggregates sugar (BS2.4)
  metrics?: {
    rate?: Array<{
      name: string
      numerator: string
      denominator: string
      unit?: "per_second" | "per_minute" | "per_hour" | "per_day"
    }>
    ratio?: Array<{
      name: string
      numerator: string
      denominator: string
      scale?: number
    }>
    time_between?: Array<{
      name: string
      start: string
      end: string
      unit?: "seconds" | "minutes" | "hours" | "days"
    }>
    group_by?: string[]
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
  stop_event: string
  within_seconds: number
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
