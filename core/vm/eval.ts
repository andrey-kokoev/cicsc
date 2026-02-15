import type { ExprV0, IntrinsicFnV0, LiteralV0, VarRefV0 } from "../ir/types"

export type Json = null | boolean | number | string | Json[] | { [k: string]: Json }

export type Value = Json

export type VmEnv = {
  now: number
  actor: string
  state: string
  input: Record<string, Value>
  attrs: Record<string, Value>
  row: Record<string, Value>
  arg: Record<string, Value>

  // assert context
  rows_count?: number
  agg?: Record<string, Value>

  // queue/event context
  payload?: any
  e?: { type: string; actor: string; time: number; payload: Record<string, Value> }

  // intrinsics
  intrinsics: VmIntrinsics
  policies?: Record<string, { params: string[]; expr: ExprV0 }>
}

export type VmIntrinsics = {
  has_role: (actor: string, role: string) => boolean
  role_of: (actor: string) => string
  auth_ok: (actor: string, cmdref: string) => boolean
  constraint: (name: string, args: Value) => boolean
  len: (v: Value) => number | null
  str: (v: Value) => string | null
  int: (v: Value) => number | null
  float: (v: Value) => number | null
}

export function evalExpr (expr: ExprV0, env: VmEnv): Value {
  const tag = soleKey(expr)
  const body: any = (expr as any)[tag]

  switch (tag) {
    case "lit":
      return evalLit(body as LiteralV0)

    case "var":
      return evalVar(body as VarRefV0, env)

    case "get": {
      const base = evalExpr(body.expr, env)
      return getPath(base, body.path)
    }

    case "has": {
      const base = evalExpr(body.expr, env)
      return hasPath(base, body.path)
    }

    case "obj": {
      const out: Record<string, Value> = {}
      for (const [k, ex] of Object.entries(body.fields as Record<string, ExprV0>)) out[k] = evalExpr(ex, env)
      return out
    }

    case "arr":
      return (body.items as ExprV0[]).map((e) => evalExpr(e, env))

    case "not":
      return !toBool(evalExpr(body, env))

    case "bool":
      return toBool(evalExpr(body, env))

    case "and":
      for (const e of body as ExprV0[]) if (!toBool(evalExpr(e, env))) return false
      return true

    case "or":
      for (const e of body as ExprV0[]) if (toBool(evalExpr(e, env))) return true
      return false

    case "eq": {
      const [a, b] = body as [ExprV0, ExprV0]
      return deepEq(evalExpr(a, env), evalExpr(b, env))
    }
    case "ne": {
      const [a, b] = body as [ExprV0, ExprV0]
      return !deepEq(evalExpr(a, env), evalExpr(b, env))
    }

    case "lt":
    case "le":
    case "gt":
    case "ge": {
      const [a, b] = body as [ExprV0, ExprV0]
      const av = evalExpr(a, env)
      const bv = evalExpr(b, env)
      if (typeof av !== "number" || typeof bv !== "number") return null
      if (tag === "lt") return av < bv
      if (tag === "le") return av <= bv
      if (tag === "gt") return av > bv
      return av >= bv
    }

    case "in": {
      const needle = evalExpr(body.needle, env)
      const hay = evalExpr(body.haystack, env)
      if (!Array.isArray(hay)) return null
      for (const item of hay) if (deepEq(item, needle)) return true
      return false
    }

    case "add":
    case "sub":
    case "mul":
    case "div": {
      const [a, b] = body as [ExprV0, ExprV0]
      const av = evalExpr(a, env)
      const bv = evalExpr(b, env)
      if (typeof av !== "number" || typeof bv !== "number") return null
      if (tag === "add") return av + bv
      if (tag === "sub") return av - bv
      if (tag === "mul") return av * bv
      if (bv === 0) return null
      return av / bv
    }

    case "if": {
      const cond = toBool(evalExpr(body.cond, env))
      return cond ? evalExpr(body.then, env) : evalExpr(body.else, env)
    }

    case "coalesce": {
      for (const e of body as ExprV0[]) {
        const v = evalExpr(e, env)
        if (v !== null) return v
      }
      return null
    }

    case "is_null":
      return evalExpr(body, env) === null

    case "time_between": {
      const [a, b] = body as [ExprV0, ExprV0]
      const av = evalExpr(a, env)
      const bv = evalExpr(b, env)
      if (typeof av !== "number" || typeof bv !== "number") return null
      return Math.trunc(bv - av)
    }

    case "map_enum": {
      const v = evalExpr(body.expr, env)
      if (typeof v !== "string") return null
      const n = (body.mapping as Record<string, number>)[v]
      return typeof n === "number" ? n : null
    }

    case "call": {
      const fn = body.fn as IntrinsicFnV0
      const args = (body.args as ExprV0[]).map((e) => evalExpr(e, env))
      return evalCall(fn, args, env)
    }

    default:
      return null
  }
}

function evalCall (fn: IntrinsicFnV0, args: Value[], env: VmEnv): Value {
  switch (fn) {
    case "has_role":
      return typeof args[0] === "string" && typeof args[1] === "string" ? env.intrinsics.has_role(args[0], args[1]) : null
    case "role_of":
      return typeof args[0] === "string" ? env.intrinsics.role_of(args[0]) : null
    case "auth_ok":
      return typeof args[0] === "string" && typeof args[1] === "string" ? env.intrinsics.auth_ok(args[0], args[1]) : null

    case "constraint":
      // args[1] is JSON object by convention
      return typeof args[0] === "string" ? env.intrinsics.constraint(args[0], args[1] ?? null) : null

    case "allowed": {
      // policy call: first arg is policy name string, remaining are policy args OR direct policy symbolization.
      // v0 simplification: treat allowed(...) as intrinsic or policy mapped by adapter/runtime.
      // If policies are provided, allow `call(fn="allowed")` to dispatch to policy named "allowed".
      const pol = env.policies?.["allowed"]
      if (!pol) return null
      const bindings: Record<string, Value> = {}
      for (let i = 0; i < pol.params.length; i++) bindings[pol.params[i]!] = args[i] ?? null
      const subEnv: VmEnv = { ...env, arg: { ...env.arg, ...bindings } }
      return toBool(evalExpr(pol.expr, subEnv))
    }

    case "len":
      return env.intrinsics.len(args[0] ?? null)
    case "str":
      return env.intrinsics.str(args[0] ?? null)
    case "int":
      return env.intrinsics.int(args[0] ?? null)
    case "float":
      return env.intrinsics.float(args[0] ?? null)

    default:
      return null
  }
}

function evalLit (lit: LiteralV0): Value {
  const tag = soleKey(lit)
  const body: any = (lit as any)[tag]
  if (tag === "null") return null
  if (tag === "bool") return !!body
  if (tag === "int" || tag === "float") return typeof body === "number" ? body : null
  if (tag === "string") return typeof body === "string" ? body : null
  return null
}

function evalVar (v: VarRefV0, env: VmEnv): Value {
  const tag = soleKey(v)
  const body: any = (v as any)[tag]

  switch (tag) {
    case "now":
      return env.now
    case "actor":
      return env.actor
    case "state":
      return env.state

    case "input":
      return env.input[body.field] ?? null
    case "attrs":
      return env.attrs[body.field] ?? null
    case "row":
      return env.row[body.field] ?? null
    case "arg":
      return env.arg[body.name] ?? null

    case "rows_count":
      return typeof env.rows_count === "number" ? env.rows_count : null
    case "agg":
      return env.agg?.[body.name] ?? null

    case "e_type":
      return env.e?.type ?? null
    case "e_actor":
      return env.e?.actor ?? null
    case "e_time":
      return env.e?.time ?? null
    case "e_payload":
      return env.e ? getPath(env.e.payload, body.path) : null

    case "payload":
      return env.payload ? getPath(env.payload, body.path) : null

    default:
      return null
  }
}

function soleKey (o: object): string {
  const ks = Object.keys(o)
  return ks.length ? ks[0]! : ""
}

function toBool (v: Value): boolean {
  if (v === null) return false
  if (typeof v === "boolean") return v
  if (typeof v === "number") return v !== 0
  if (typeof v === "string") return v.length > 0
  if (Array.isArray(v)) return v.length > 0
  return Object.keys(v).length > 0
}

function deepEq (a: Value, b: Value): boolean {
  if (a === b) return true
  if (a === null || b === null) return false
  if (typeof a !== typeof b) return false
  if (typeof a !== "object") return false
  if (Array.isArray(a) !== Array.isArray(b)) return false

  if (Array.isArray(a) && Array.isArray(b)) {
    if (a.length !== b.length) return false
    for (let i = 0; i < a.length; i++) if (!deepEq(a[i] as any, b[i] as any)) return false
    return true
  }

  const ao = a as Record<string, Value>
  const bo = b as Record<string, Value>
  const aks = Object.keys(ao).sort()
  const bks = Object.keys(bo).sort()
  if (aks.length !== bks.length) return false
  for (let i = 0; i < aks.length; i++) {
    const k = aks[i]!
    if (k !== bks[i]) return false
    if (!deepEq(ao[k] ?? null, bo[k] ?? null)) return false
  }
  return true
}

function getPath (v: Value, path: string): Value {
  if (v === null) return null
  const parts = path.split(".").filter(Boolean)
  let cur: any = v
  for (const p of parts) {
    if (cur === null) return null
    if (typeof cur !== "object") return null
    cur = (cur as any)[p]
    if (cur === undefined) return null
  }
  return (cur as any) ?? null
}

function hasPath (v: Value, path: string): Value {
  if (v === null) return false
  const parts = path.split(".").filter(Boolean)
  let cur: any = v
  for (const p of parts) {
    if (cur === null) return false
    if (typeof cur !== "object") return false
    if (!Object.prototype.hasOwnProperty.call(cur, p)) return false
    cur = cur[p]
  }
  return true
}
