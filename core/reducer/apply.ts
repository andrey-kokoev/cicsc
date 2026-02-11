// /core/reducer/apply.ts

import type { ReducerOpV0 } from "../ir/types"
import type { Value } from "../vm/eval"

export type Snapshot = {
  state: string
  attrs: Record<string, Value>
  shadows: Record<string, Value>
  updated_ts: number
}

export function applyReducerOps (params: {
  snapshot: Snapshot
  ops: ReducerOpV0[]
  eval: (expr: any) => Value
  now: number
}): Snapshot {
  const { snapshot, ops, eval: evalExpr, now } = params
  const next: Snapshot = {
    state: snapshot.state,
    attrs: { ...snapshot.attrs },
    shadows: { ...snapshot.shadows },
    updated_ts: now,
  }

  for (const op of ops) {
    const tag = soleKey(op)
    const body: any = (op as any)[tag]

    switch (tag) {
      case "set_state": {
        const v = evalExpr(body.expr)
        if (typeof v === "string") next.state = v
        break
      }
      case "set_attr": {
        const v = evalExpr(body.expr)
        next.attrs[body.name] = v
        break
      }
      case "clear_attr": {
        delete next.attrs[body.name]
        break
      }
      case "set_shadow": {
        const v = evalExpr(body.expr)
        next.shadows[body.name] = v
        break
      }
    }
  }

  return next
}

function soleKey (o: object): string {
  const ks = Object.keys(o)
  return ks.length ? ks[0]! : ""
}
