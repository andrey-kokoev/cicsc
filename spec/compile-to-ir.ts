import type { CoreIrV0 } from "../core/ir/types"
import type { SpecV0 } from "./ast"

export function compileSpecV0ToCoreIr (spec: SpecV0): CoreIrV0 {
  const types: CoreIrV0["types"] = {}
  for (const [name, e] of Object.entries(spec.entities ?? {})) {
    types[name] = {
      id_type: e.id,
      states: e.states,
      initial_state: e.initial,
      attrs: e.attributes ?? {},
      shadows: e.shadows ?? {},
      commands: mapCommands(e.commands ?? {}, name),
      reducer: mapReducers(e.reducers ?? {}),
      row_policy: e.row_policy ? lowerRowPolicy(e.row_policy) : undefined,
    } as any
  }

  const constraints = mapConstraints(spec.constraints ?? {})
  const views = mapViews(spec.views ?? {})
  const slas = mapSlas(spec.slas ?? {})
  const migrations = mapMigrations(spec.migrations ?? {})
  const policies = mapPolicies(spec.policies ?? {})
  const subscriptions = mapSubscriptions(spec.subscriptions ?? {})
  const webhooks = mapWebhooks(spec.webhooks ?? {})
  const rowPolicies = mapRowPolicies(spec.row_policies ?? {})

  return {
    version: 0,
    types,
    policies: Object.keys(policies).length ? policies : undefined,
    constraints: Object.keys(constraints).length ? constraints : undefined,
    views: Object.keys(views).length ? views : undefined,
    slas: Object.keys(slas).length ? slas : undefined,
    migrations: Object.keys(migrations).length ? migrations : undefined,
    subscriptions: Object.keys(subscriptions).length ? subscriptions : undefined,
    webhooks: Object.keys(webhooks).length ? webhooks : undefined,
    row_policies: Object.keys(rowPolicies).length ? rowPolicies : undefined,
  }
}

function mapCommands (commands: Record<string, any>, entityName: string) {
  const out: Record<string, any> = {}
  for (const [name, c] of Object.entries(commands)) {
    const baseGuard = lowerGuard((c as any).when)
    const authGuard = lowerAuthGuard((c as any).auth, entityName, name)
    const guardExpr = authGuard ? { and: [baseGuard, authGuard] } : baseGuard

    out[name] = {
      input: c.inputs ?? {},
      guard: { expr: guardExpr },
      emits: (c.emit ?? []).map((x: any) => ({
        event_type: String(x.type),
        payload: x.payload ?? {},
      })),
    }
  }
  return out
}

function lowerAuthGuard (auth: any, entityName: string, commandName: string): any | null {
  if (!auth || typeof auth !== "object" || Array.isArray(auth)) return null
  const cmdref = String(auth.cmdref ?? auth.policy ?? `${entityName}.${commandName}`)
  return {
    call: {
      fn: "auth_ok",
      args: [{ var: { actor: true } }, { lit: { string: cmdref } }],
    },
  }
}

function lowerGuard (when: any): any {
  if (when == null) return { lit: { bool: true } }
  if (isExprTaggedObject(when)) return when
  if (!when || typeof when !== "object" || Array.isArray(when)) {
    throw new Error("guard sugar must be an object")
  }

  if (Array.isArray((when as any).all)) {
    return { and: (when as any).all.map((x: any) => lowerGuard(x)) }
  }
  if (Array.isArray((when as any).any)) {
    return { or: (when as any).any.map((x: any) => lowerGuard(x)) }
  }

  const parts: any[] = []
  if (typeof (when as any).state_is === "string") {
    parts.push({
      eq: [
        { var: { state: true } },
        { lit: { string: String((when as any).state_is) } },
      ],
    })
  }
  if (typeof (when as any).role_is === "string") {
    parts.push({
      call: {
        fn: "has_role",
        args: [{ var: { actor: true } }, { lit: { string: String((when as any).role_is) } }],
      },
    })
  }

  if (!parts.length) throw new Error("unsupported guard sugar shape")
  if (parts.length === 1) return parts[0]
  return { and: parts }
}

function mapConstraints (constraints: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, c] of Object.entries(constraints)) {
    if (c.kind === "snapshot") {
      out[name] = { kind: "snapshot", on_type: c.entity, expr: c.when }
    } else if (c.kind === "bool_query") {
      out[name] = {
        kind: "bool_query",
        on_type: c.entity,
        args: c.args ?? {},
        query: c.query,
        assert: c.assert,
      }
    } else {
      throw new Error(`unknown constraint kind: ${String((c as any)?.kind ?? "?")}`)
    }
  }
  return out
}

function mapViews (views: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, v] of Object.entries(views)) {
    const query = v.query ?? lowerViewSugar(v)
    out[name] = {
      kind: v.kind ?? "metric",
      on_type: v.on,
      query,
      row_policy: v.row_policy ? lowerRowPolicy(v.row_policy) : undefined,
    }
  }
  return out
}

function mapMigrations (migrations: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, m] of Object.entries(migrations ?? {})) {
    const from = Number((m as any).from)
    const to = Number((m as any).to)
    if (!Number.isInteger(from) || !Number.isInteger(to) || to !== from + 1) {
      throw new Error(`migration '${name}' must define adjacent versions (from N to N+1)`)
    }

    out[name] = {
      from_version: from,
      to_version: to,
      on_type: String((m as any).entity ?? ""),
      event_transforms: mapEventTransforms((m as any).event_transforms ?? {}),
      state_map: (m as any).state_map ?? undefined,
    }
  }
  return out
}

function mapPolicies (policies: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, p] of Object.entries(policies ?? {})) {
    out[name] = {
      params: Array.isArray((p as any).params) ? (p as any).params.map(String) : [],
      expr: lowerGuard((p as any).allow ?? null),
    }
  }
  return out
}

function mapSlas (slas: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, s] of Object.entries(slas ?? {})) {
    out[name] = {
      name,
      on_type: String((s as any).on ?? ""),
      start: { event: { name: String((s as any).start_event ?? "") } },
      stop: { event: { name: String((s as any).stop_event ?? "") } },
      within_seconds: Number((s as any).within_seconds ?? 0),
      enforce: { none: true },
    }
  }
  return out
}

function mapEventTransforms (eventTransforms: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [eventType, t] of Object.entries(eventTransforms ?? {})) {
    const transform: any = {
      emit_as: typeof (t as any)?.emit_as === "string" ? (t as any).emit_as : undefined,
      payload_map: (t as any)?.payload_map ?? undefined,
      drop: Boolean((t as any)?.drop ?? false),
    }
    
    // BQ1.1: Handle emit_many for fan-out
    if (Array.isArray((t as any).emit_many)) {
      transform.emit_many = (t as any).emit_many.map((e: any) => ({
        event_type: String(e.event_type ?? e.type),
        payload: e.payload ?? e.payload_map ?? {},
      }))
    }
    
    out[eventType] = transform
  }
  return out
}

function mapReducers (reducers: Record<string, any[]>): Record<string, any[]> {
  const out: Record<string, any[]> = {}
  for (const [eventType, ops] of Object.entries(reducers ?? {})) {
    out[eventType] = (ops ?? []).map((op) => lowerReducerOp(op))
  }
  return out
}

function lowerReducerOp (op: any): any {
  if (!op || typeof op !== "object" || Array.isArray(op)) throw new Error("reducer op must be an object")
  const tag = Object.keys(op)[0]
  const body = (op as any)[tag]

  if (tag === "set_state") {
    if (body && typeof body === "object" && "expr" in body) return op
    return { set_state: { expr: wrapExpr(body) } }
  }

  if (tag === "set_attr") {
    if (body && typeof body === "object" && "name" in body && "expr" in body) return op
    if (body && typeof body === "object" && typeof body.field === "string" && "value" in body) {
      return { set_attr: { name: body.field, expr: wrapExpr(body.value) } }
    }
    throw new Error("set_attr sugar expects { field, value }")
  }

  if (tag === "set_shadow") {
    if (body && typeof body === "object" && "name" in body && "expr" in body) return op
    if (body && typeof body === "object" && typeof body.field === "string" && "value" in body) {
      return { set_shadow: { name: body.field, expr: wrapExpr(body.value) } }
    }
    throw new Error("set_shadow sugar expects { field, value }")
  }

  if (tag === "clear_attr") {
    if (body && typeof body === "object" && typeof body.name === "string") return op
    if (typeof body === "string") return { clear_attr: { name: body } }
    throw new Error("clear_attr sugar expects string attr name")
  }

  return op
}

const EXPR_TAGS = new Set([
  "lit", "var", "get", "has", "obj", "arr",
  "not", "and", "or", "bool",
  "eq", "ne", "lt", "le", "gt", "ge", "in",
  "add", "sub", "mul", "div",
  "if", "coalesce", "is_null",
  "time_between", "map_enum",
  "call",
])

function isExprTaggedObject (v: any): boolean {
  if (!v || typeof v !== "object" || Array.isArray(v)) return false
  const ks = Object.keys(v)
  return ks.length === 1 && EXPR_TAGS.has(ks[0]!)
}

function wrapExpr (v: any): any {
  if (isExprTaggedObject(v)) return v
  if (v === null) return { lit: { null: true } }
  if (typeof v === "boolean") return { lit: { bool: v } }
  if (typeof v === "number") return Number.isInteger(v) ? { lit: { int: v } } : { lit: { float: v } }
  if (typeof v === "string") return { lit: { string: v } }
  throw new Error("unsupported reducer sugar literal")
}

function lowerViewSugar (v: any): any {
  if (!v || typeof v !== "object") throw new Error("view must be object")
  
  // Handle rich aggregates metrics sugar (BS2.4)
  if (v.metrics && typeof v.metrics === "object") {
    return lowerMetricsSugar(v)
  }
  
  if (!v.lanes || typeof v.lanes !== "object") throw new Error("view.query missing and no lanes/metrics sugar provided")

  const lanes = v.lanes as any
  const pipeline: any[] = []

  if (Array.isArray(lanes.states) && lanes.states.length > 0) {
    pipeline.push({
      filter: {
        in: {
          needle: { var: { row: { field: "state" } } },
          haystack: { arr: { items: lanes.states.map((s: string) => ({ lit: { string: String(s) } })) } },
        },
      },
    })
  }

  if (lanes.order_by && typeof lanes.order_by === "object" && typeof lanes.order_by.field === "string") {
    pipeline.push({
      order_by: [
        {
          expr: { var: { row: { field: lanes.order_by.field } } },
          dir: lanes.order_by.dir === "asc" ? "asc" : "desc",
        },
      ],
    })
  }

  if (typeof lanes.limit === "number") {
    pipeline.push({ limit: Math.max(0, Math.trunc(lanes.limit)) })
  }

  return {
    source: { snap: { type: String(v.on) } },
    pipeline,
  }
}

function lowerMetricsSugar (v: any): any {
  const metrics = v.metrics as any
  const pipeline: any[] = []
  const aggs: Record<string, any> = {}
  
  // Build aggregations from metrics sugar
  if (Array.isArray(metrics.rate)) {
    for (const r of metrics.rate) {
      aggs[r.name] = {
        rate: {
          numerator: { var: { row: { field: r.numerator } } },
          denominator: { var: { row: { field: r.denominator } } },
          unit: r.unit ?? "per_hour",
        },
      }
    }
  }
  
  if (Array.isArray(metrics.ratio)) {
    for (const r of metrics.ratio) {
      aggs[r.name] = {
        ratio: {
          numerator: { var: { row: { field: r.numerator } } },
          denominator: { var: { row: { field: r.denominator } } },
          scale: r.scale ?? 1,
        },
      }
    }
  }
  
  if (Array.isArray(metrics.time_between)) {
    for (const t of metrics.time_between) {
      aggs[t.name] = {
        time_between: {
          start_expr: { var: { row: { field: t.start } } },
          end_expr: { var: { row: { field: t.end } } },
          unit: t.unit ?? "seconds",
        },
      }
    }
  }
  
  // Add standard count aggregation
  aggs.count = { count: {} }
  
  // Build group_by keys
  const keys = Array.isArray(metrics.group_by) 
    ? metrics.group_by.map((field: string) => ({ name: field, expr: { var: { row: { field } } } }))
    : []
  
  pipeline.push({
    group_by: { keys, aggs },
  })
  
  return {
    source: { snap: { type: String(v.on) } },
    pipeline,
  }
}

function mapSubscriptions (subscriptions: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, s] of Object.entries(subscriptions)) {
    out[name] = {
      on_type: String(s.on),
      filter: s.filter ? lowerSubscriptionFilter(s.filter) : undefined
    }
  }
  return out
}

function lowerSubscriptionFilter (filter: any): any {
  if (filter == null) return filter
  if (typeof filter !== "object") return filter

  if (filter.var && filter.var.input) {
    return { var: { row: { field: filter.var.input.field } } }
  }

  if (Array.isArray(filter)) {
    return filter.map(x => lowerSubscriptionFilter(x))
  }

  const out: any = {}
  for (const [k, v] of Object.entries(filter)) {
    out[k] = lowerSubscriptionFilter(v)
  }
  return out
}

function mapWebhooks (webhooks: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, w] of Object.entries(webhooks)) {
    out[name] = {
      on_type: String(w.on),
      command: String(w.command),
      verify: w.verify
    }
  }
  return out
}

// Row-Level Security policy map (BT2.1-BT2.3)
function mapRowPolicies (rowPolicies: Record<string, any>): Record<string, any> {
  const out: Record<string, any> = {}
  for (const [name, policy] of Object.entries(rowPolicies)) {
    out[name] = lowerRowPolicy(policy)
  }
  return out
}

// Row-Level Security policy lowering (BT2.1-BT2.3)
function lowerRowPolicy (policy: any): any {
  if (typeof policy === "string") {
    // Named policy reference - will be resolved at validation time
    return { ref: policy }
  }

  if (!policy || typeof policy !== "object") {
    throw new Error("row_policy must be an object or string reference")
  }

  const keys = Object.keys(policy)
  if (keys.length !== 1) {
    throw new Error("row_policy must have exactly one key (owner, member_of, or expr)")
  }

  const tag = keys[0]!
  const body = policy[tag]

  switch (tag) {
    case "owner":
      return {
        owner: {
          actor_field: String(body.field)
        }
      }
    case "member_of":
      return {
        member_of: {
          actor_field: String(body.field),
          target_type: String(body.through),
          target_field: body.target_field ? String(body.target_field) : "entity_id"
        }
      }
    case "expr":
      return { expr: body }
    default:
      throw new Error(`unknown row_policy tag: ${tag}`)
  }
}
