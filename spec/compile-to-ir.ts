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
      reducer: e.reducers ?? {},
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
    out[name] = {
      kind: v.kind ?? "metric",
      on_type: v.on,
      query: v.query,
    }
  }
  return out
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
