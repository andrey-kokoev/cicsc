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
      guard: { expr: c.when ?? { lit: { bool: true } } },
      emits: (c.emit ?? []).map((x: any) => ({
        event_type: String(x.type),
        payload: x.payload ?? {},
      })),
    }
  }
  return out
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
