// /spec/ast.ts

export type SpecV0 = {
  version: 0

  types: Record<string, SpecTypeV0>
  constraints?: Record<string, SpecConstraintV0>
  views?: Record<string, SpecViewV0>
}

export type SpecTypeV0 = {
  id_type: "string"
  states: string[]
  initial_state: string

  attrs?: Record<string, SpecAttrV0>
  shadows?: Record<string, SpecShadowV0>

  commands?: Record<string, SpecCommandV0>
  reducer?: Record<string, any[]>
}

export type SpecAttrV0 = {
  type: "string" | "int" | "float" | "bool" | "time" | "enum"
  optional?: boolean
  values?: string[] // for enum
}

export type SpecShadowV0 = {
  type: "string" | "int" | "float" | "bool" | "time" | "enum"
}

export type SpecCommandV0 = {
  input?: Record<string, SpecAttrV0>
  guard?: any // Expr DSL (same tagged-object form)
  emits: Array<{ event_type: string; payload?: Record<string, any> }>
}

export type SpecConstraintV0 =
  | { kind: "snapshot"; on_type: string; expr: any }
  | { kind: "bool_query"; on_type: string; args?: Record<string, SpecAttrV0>; query: any; assert: any }

export type SpecViewV0 = {
  kind: string
  on_type: string
  query: any;
  [k: string]: any
}
