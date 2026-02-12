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
      commands: mapCommands(e.commands ?? {}),
      reducer: mapReducers(e.reducers ?? {}),
    } as any
  }

  const constraints = mapConstraints(spec.constraints ?? {})
  const views = mapViews(spec.views ?? {})

  return {
    version: 0,
    types,
    constraints: Object.keys(constraints).length ? constraints : undefined,
    views: Object.keys(views).length ? views : undefined,
  }
}

function mapCommands (commands: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, c] of Object.entries(commands)) {
    out[name] = {
      input: c.inputs ?? {},
      guard: { expr: lowerGuard(c.when) },
      emits: (c.emit ?? []).map((x: any) => ({
        event_type: String(x.type),
        payload: x.payload ?? {},
      })),
    }
  }
  return out
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
    }
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
  if (!v.lanes || typeof v.lanes !== "object") throw new Error("view.query missing and no lanes sugar provided")

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
