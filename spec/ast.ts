export type SpecV0 = {
  version: 0
  entities: Record<string, SpecEntityV0>
  constraints?: Record<string, SpecConstraintV0>
  views?: Record<string, SpecViewV0>
  migrations?: Record<string, SpecMigrationV0>
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
  emit: Array<{ type: string; payload?: Record<string, any> }>
}

export type SpecConstraintV0 =
  | { kind: "snapshot"; entity: string; when: any }
  | { kind: "bool_query"; entity: string; args?: Record<string, SpecAttrV0>; query: any; assert: any }

export type SpecViewV0 = {
  kind: string
  on: string
  query?: any
  lanes?: {
    states?: string[]
    order_by?: { field: string; dir?: "asc" | "desc" }
    limit?: number
  }
  [k: string]: any
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
