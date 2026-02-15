import type { AggExprV0, ExprV0, OpV0, QueryV0, SourceV0 } from "../ir/types"
import { evalExpr, type VmEnv, type Value } from "../vm/eval"

export type SnapRow = Record<string, Value> // includes entity_id, state, attrs.*, shadows.*, updated_ts, etc.
export type SlaRow = Record<string, Value>  // includes entity_id, breached, deadline_ts, etc.

export type QueryContext = {
  now: number
  actor: string

  // data sources
  snap: (typeName: string) => SnapRow[]
  sla_status: (name: string, onType: string) => SlaRow[]

  // vm intrinsics + policies for expr evaluation in filters/order keys
  baseEnv: Omit<VmEnv, "row">
}

export function interpretQuery (q: QueryV0, ctx: QueryContext): { rows: Record<string, Value>[]; rows_count: number } {
  let rows = materializeSource(q.source, ctx)

  for (const op of q.pipeline) {
const tag = soleKey(op)
    const body: any = (op as any)[tag]

    switch (tag) {
      case "filter":
        rows = rows.filter((r) => toBool(evalInRow(body as ExprV0, r, ctx)))
        break

      case "project":
        rows = rows.map((r) => {
          const out: Record<string, Value> = {}
          for (const f of body.fields as { name: string; expr: ExprV0 }[]) out[f.name] = evalInRow(f.expr, r, ctx)
          return out
        })
        break

      case "group_by":
        rows = groupBy(rows, body.keys, body.aggs, ctx)
        break

      case "having":
        rows = rows.filter((r) => toBool(evalInRow(body as ExprV0, r, ctx)))
        break

      case "order_by":
        rows = stableSort(rows, body, (expr: ExprV0, row: Record<string, Value>) => evalInRow(expr, row, ctx))
        break

      case "limit":
        rows = rows.slice(0, Math.max(0, body as number))
        break

      case "offset":
        rows = rows.slice(Math.max(0, body as number))
        break

      default:
        throw new Error(`interpretQuery: unsupported op '${tag}'`)
    }
  }

  return { rows, rows_count: rows.length }
}

function materializeSource (src: SourceV0, ctx: QueryContext): Record<string, Value>[] {
  const tag = soleKey(src)
  const body: any = (src as any)[tag]

  switch (tag) {
    case "snap":
      return ctx.snap(body.type)

    case "sla_status":
      return ctx.sla_status(body.name, body.on_type)

    case "join": {
      const left = materializeSource(body.left, ctx)
      const right = materializeSource(body.right, ctx)
      const lf = body.on.left_field as string
      const rf = body.on.right_field as string

      // v0: equi-join. Namespacing: left.<field>, right.<field>
      const index = new Map<string, Record<string, Value>[]>()
      for (const r of right) {
        const key = String(r[rf] ?? "")
        const arr = index.get(key)
        if (arr) arr.push(r)
        else index.set(key, [r])
      }

      const out: Record<string, Value>[] = []
      for (const l of left) {
        const key = String(l[lf] ?? "")
        const matches = index.get(key)
        if (!matches) continue
        for (const r of matches) {
          out.push(namespaceRow(l, "left", r, "right"))
        }
      }
      return out
    }

    default:
      return []
  }
}

function namespaceRow (a: Record<string, Value>, an: string, b: Record<string, Value>, bn: string): Record<string, Value> {
  const out: Record<string, Value> = {}
  for (const [k, v] of Object.entries(a)) {
    out[`${an}.${k}`] = v
    if (!(k in out)) out[k] = v
  }
  for (const [k, v] of Object.entries(b)) {
    out[`${bn}.${k}`] = v
    if (!(k in out)) out[k] = v
  }
  return out
}

function evalInRow (expr: ExprV0, row: Record<string, Value>, ctx: QueryContext): Value {
  const env: VmEnv = {
    ...(ctx.baseEnv as any),
    now: ctx.now,
    actor: ctx.actor,
    state: (ctx.baseEnv as any).state ?? "",
    input: (ctx.baseEnv as any).input ?? {},
    attrs: (ctx.baseEnv as any).attrs ?? {},
    arg: (ctx.baseEnv as any).arg ?? {},
    row,
    intrinsics: (ctx.baseEnv as any).intrinsics,
    policies: (ctx.baseEnv as any).policies,
  }
  return evalExpr(expr, env)
}

function groupBy (
  rows: Record<string, Value>[],
  keys: { name: string; expr: ExprV0 }[],
  aggs: Record<string, AggExprV0>,
  ctx: QueryContext
): Record<string, Value>[] {
  // Evaluate keys, group by key tuple string, compute aggs.
  const groups = new Map<string, { keyObj: Record<string, Value>; rows: Record<string, Value>[] }>()

  for (const row of rows) {
    const keyObj: Record<string, Value> = {}
    for (const k of keys) keyObj[k.name] = evalInRow(k.expr, row, ctx)
    const keyStr = JSON.stringify(keyObj, stableJsonReplacer)
    const g = groups.get(keyStr)
    if (g) g.rows.push(row)
    else groups.set(keyStr, { keyObj, rows: [row] })
  }

  const out: Record<string, Value>[] = []
  for (const g of groups.values()) {
    const rec: Record<string, Value> = { ...g.keyObj }
    for (const [aggName, aggSpec] of Object.entries(aggs)) rec[aggName] = computeAgg(aggSpec, g.rows, ctx)
    out.push(rec)
  }
  return out
}

function computeAgg (agg: AggExprV0, rows: Record<string, Value>[], ctx: QueryContext): Value {
  const tag = soleKey(agg)
  const body: any = (agg as any)[tag]

  switch (tag) {
    case "count":
      return rows.length

    case "sum": {
      let s = 0
      let ok = false
      for (const r of rows) {
        const v = evalInRow(body.expr, r, ctx)
        if (typeof v === "number") {
          s += v
          ok = true
        }
      }
      return ok ? s : null
    }

    case "min": {
      let m: number | null = null
      for (const r of rows) {
        const v = evalInRow(body.expr, r, ctx)
        if (typeof v === "number") m = m === null ? v : Math.min(m, v)
      }
      return m
    }

    case "max": {
      let m: number | null = null
      for (const r of rows) {
        const v = evalInRow(body.expr, r, ctx)
        if (typeof v === "number") m = m === null ? v : Math.max(m, v)
      }
      return m
    }

    case "rate": {
      let numSum = 0
      let denSum = 0
      for (const r of rows) {
        const num = evalInRow(body.numerator, r, ctx)
        const den = evalInRow(body.denominator, r, ctx)
        if (typeof num === "number") numSum += num
        if (typeof den === "number") denSum += den
      }
      if (denSum === 0) return null
      const rate = numSum / denSum
      // Convert to requested unit
      const multiplier: Record<string, number> = {
        per_second: 1,
        per_minute: 60,
        per_hour: 3600,
        per_day: 86400,
      }
      return rate * (multiplier[body.unit] ?? 1)
    }

    case "ratio": {
      let numSum = 0
      let denSum = 0
      for (const r of rows) {
        const num = evalInRow(body.numerator, r, ctx)
        const den = evalInRow(body.denominator, r, ctx)
        if (typeof num === "number") numSum += num
        if (typeof den === "number") denSum += den
      }
      if (denSum === 0) return null
      const scale = body.scale ?? 1
      return (numSum / denSum) * scale
    }

    case "time_between": {
      let total = 0
      let count = 0
      for (const r of rows) {
        const start = evalInRow(body.start_expr, r, ctx)
        const end = evalInRow(body.end_expr, r, ctx)
        if (typeof start === "number" && typeof end === "number") {
          total += end - start
          count++
        }
      }
      if (count === 0) return null
      const avgSeconds = total / count
      // Convert to requested unit
      const divisor: Record<string, number> = {
        seconds: 1,
        minutes: 60,
        hours: 3600,
        days: 86400,
      }
      return avgSeconds / (divisor[body.unit ?? "seconds"] ?? 1)
    }

    default:
      return null
  }
}

function stableSort (
  rows: Record<string, Value>[],
  orderKeys: { expr: ExprV0; dir: "asc" | "desc" }[],
  evalKey: (expr: ExprV0, row: Record<string, Value>) => Value
): Record<string, Value>[] {
  const decorated = rows.map((r, i) => ({ r, i, ks: orderKeys.map((k) => evalKey(k.expr, r)) }))
  decorated.sort((a, b) => {
    for (let j = 0; j < orderKeys.length; j++) {
      const dir = orderKeys[j]!.dir
      const av = a.ks[j]
      const bv = b.ks[j]
      const cmp = compareValues(av, bv)
      if (cmp !== 0) return dir === "asc" ? cmp : -cmp
    }
    return a.i - b.i
  })
  return decorated.map((d) => d.r)
}

function compareValues (a: Value, b: Value): number {
  if (a === b) return 0
  if (a === null) return -1
  if (b === null) return 1
  if (typeof a === "number" && typeof b === "number") return a < b ? -1 : 1
  if (typeof a === "string" && typeof b === "string") return a < b ? -1 : 1
  if (typeof a === "boolean" && typeof b === "boolean") return (a === false && b === true) ? -1 : 1
  // fallback: stringify
  const as = JSON.stringify(a, stableJsonReplacer)
  const bs = JSON.stringify(b, stableJsonReplacer)
  return as < bs ? -1 : 1
}

function toBool (v: Value): boolean {
  if (v === null) return false
  if (typeof v === "boolean") return v
  if (typeof v === "number") return v !== 0
  if (typeof v === "string") return v.length > 0
  if (Array.isArray(v)) return v.length > 0
  return Object.keys(v).length > 0
}

function soleKey (o: object): string {
  const ks = Object.keys(o)
  return ks.length ? ks[0]! : ""
}

// stable JSON stringify helper
function stableJsonReplacer (this: any, key: string, value: any) {
  if (value && typeof value === "object" && !Array.isArray(value)) {
    const out: any = {}
    for (const k of Object.keys(value).sort()) out[k] = value[k]
    return out
  }
  return value
}
