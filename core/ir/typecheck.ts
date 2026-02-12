import type { CoreIrV0 } from "./types"

export type TypecheckError = {
  code:
  | "UNKNOWN_TYPE"
  | "UNKNOWN_VIEW"
  | "UNKNOWN_CONSTRAINT"
  | "UNKNOWN_COMMAND"
  | "UNKNOWN_EVENT"
  | "UNKNOWN_ATTR"
  | "UNKNOWN_SHADOW"
  | "ILLEGAL_ROW_FIELD"
  | "ILLEGAL_EXPR"
  | "ILLEGAL_INTRINSIC"
  | "ILLEGAL_REDUCER_WRITE"
  | "SHADOW_TYPE_MISMATCH"
  path: string
  message: string
}

export type TypecheckResult =
  | { ok: true; warnings: TypecheckError[] }
  | { ok: false; errors: TypecheckError[]; warnings: TypecheckError[] }

const CORE_ROW_FIELDS = new Set(["entity_id", "state", "updated_ts", "attrs_json"])

export function typecheckCoreIrV0 (ir: CoreIrV0): TypecheckResult {
  const errors: TypecheckError[] = []
  const warnings: TypecheckError[] = []

  const typeNames = new Set(Object.keys(ir.types ?? {}))

  // 0) Cross-type shadow type consistency
  {
    const byShadow = new Map<string, { typeName: string; path: string; declaredType: string | null }[]>()

    for (const [typeName, tSpecAny] of Object.entries(ir.types ?? {})) {
      const tSpec: any = tSpecAny
      for (const [shadowName, sAny] of Object.entries(tSpec.shadows ?? {})) {
        const s: any = sAny
        const declaredType = typeof s?.type === "string" && s.type.trim() !== "" ? s.type.trim() : null
        const arr = byShadow.get(shadowName) ?? []
        arr.push({
          typeName,
          path: `${typeName}.shadows.${shadowName}.type`,
          declaredType,
        })
        byShadow.set(shadowName, arr)
      }
    }

    for (const [shadowName, entries] of byShadow.entries()) {
      const explicit = new Set(entries.map((e) => e.declaredType).filter((x): x is string => x != null))

      if (explicit.size > 1) {
        const got = Array.from(explicit).sort().join(", ")
        for (const e of entries) {
          errors.push({
            code: "SHADOW_TYPE_MISMATCH",
            path: e.path,
            message: `shadow '${shadowName}' has inconsistent types across entity types: ${got}`,
          })
        }
        continue
      }

      if (explicit.size === 1 && entries.some((e) => e.declaredType == null)) {
        const only = Array.from(explicit)[0]!
        for (const e of entries) {
          if (e.declaredType != null) continue
          errors.push({
            code: "SHADOW_TYPE_MISMATCH",
            path: e.path,
            message: `shadow '${shadowName}' type must be explicitly '${only}' to match other entity types`,
          })
        }
      }
    }
  }

  // 1) Per-type checks
  for (const [tName, tSpecAny] of Object.entries(ir.types ?? {})) {
    const tSpec: any = tSpecAny

    const attrs = new Set(Object.keys(tSpec.attrs ?? {}))
    const shadows = new Set(Object.keys(tSpec.shadows ?? {}))
    const reducer = tSpec.reducer ?? {}
    const commands = tSpec.commands ?? {}

    // commands: walk guard + emits payload
    for (const [cmdName, cmdAny] of Object.entries(commands)) {
      const cmd: any = cmdAny

      walkExpr(cmd?.guard?.expr, `${tName}.commands.${cmdName}.guard.expr`, {
        allowedRowFields: buildAllowedRowFields(shadows),
        attrs,
        errors,
        allowSqlOnlyIntrinsics: false,
      })

      for (let i = 0; i < (cmd?.emits?.length ?? 0); i++) {
        const em = cmd.emits[i]
        for (const [k, ex] of Object.entries(em.payload ?? {})) {
          walkExpr(ex, `${tName}.commands.${cmdName}.emits[${i}].payload.${k}`, {
            allowedRowFields: buildAllowedRowFields(shadows),
            attrs,
            errors,
            allowSqlOnlyIntrinsics: false,
          })
        }
      }
    }

    // reducer ops: ensure writes target declared attrs/shadows; validate expressions
    for (const [eventType, ops] of Object.entries(reducer)) {
      if (!Array.isArray(ops)) {
        errors.push({
          code: "ILLEGAL_EXPR",
          path: `${tName}.reducer.${eventType}`,
          message: "reducer entry must be an array",
        })
        continue
      }

      for (let i = 0; i < ops.length; i++) {
        const op: any = ops[i]
        const tag = soleKey(op)
        const body = op[tag]

        if (tag === "set_attr") {
          const name = String(body?.name ?? "")
          if (!attrs.has(name)) {
            errors.push({
              code: "ILLEGAL_REDUCER_WRITE",
              path: `${tName}.reducer.${eventType}[${i}].set_attr.name`,
              message: `writes undeclared attr '${name}'`,
            })
          }
          walkExpr(body?.expr, `${tName}.reducer.${eventType}[${i}].set_attr.expr`, {
            allowedRowFields: buildAllowedRowFields(shadows),
            attrs,
            errors,
            allowSqlOnlyIntrinsics: false,
          })
        } else if (tag === "set_shadow") {
          const name = String(body?.name ?? "")
          if (!shadows.has(name)) {
            errors.push({
              code: "ILLEGAL_REDUCER_WRITE",
              path: `${tName}.reducer.${eventType}[${i}].set_shadow.name`,
              message: `writes undeclared shadow '${name}'`,
            })
          }
          walkExpr(body?.expr, `${tName}.reducer.${eventType}[${i}].set_shadow.expr`, {
            allowedRowFields: buildAllowedRowFields(shadows),
            attrs,
            errors,
            allowSqlOnlyIntrinsics: false,
          })
        } else if (tag === "set_state") {
          walkExpr(body?.expr, `${tName}.reducer.${eventType}[${i}].set_state.expr`, {
            allowedRowFields: buildAllowedRowFields(shadows),
            attrs,
            errors,
            allowSqlOnlyIntrinsics: false,
          })
        } else {
          errors.push({
            code: "ILLEGAL_EXPR",
            path: `${tName}.reducer.${eventType}[${i}]`,
            message: `unknown reducer op '${tag}'`,
          })
        }
      }
    }
  }

  // 2) Views: enforce row.field legality + attrs access conventions
  for (const [viewName, vAny] of Object.entries(ir.views ?? {})) {
    const v: any = vAny
    const onType = String(v.on_type ?? "")
    if (!typeNames.has(onType)) {
      errors.push({ code: "UNKNOWN_TYPE", path: `views.${viewName}.on_type`, message: `unknown type '${onType}'` })
      continue
    }
    const tSpec: any = ir.types[onType]
    const shadows = new Set(Object.keys(tSpec.shadows ?? {}))
    const attrs = new Set(Object.keys(tSpec.attrs ?? {}))

    // SQL-lowered subset must not use arbitrary intrinsics; keep it strict here.
    walkQuery(v.query, `views.${viewName}.query`, {
      allowedRowFields: buildAllowedRowFields(shadows),
      attrs,
      errors,
      allowSqlOnlyIntrinsics: true,
    })
  }

  // 3) Constraints
  for (const [cid, cAny] of Object.entries(ir.constraints ?? {})) {
    const c: any = cAny
    const kind = String(c.kind ?? "")
    const onType = String(c.on_type ?? "")
    if (!typeNames.has(onType)) {
      errors.push({ code: "UNKNOWN_TYPE", path: `constraints.${cid}.on_type`, message: `unknown type '${onType}'` })
      continue
    }
    const tSpec: any = ir.types[onType]
    const shadows = new Set(Object.keys(tSpec.shadows ?? {}))
    const attrs = new Set(Object.keys(tSpec.attrs ?? {}))

    if (kind === "snapshot") {
      walkExpr(c.expr, `constraints.${cid}.expr`, {
        allowedRowFields: buildAllowedRowFields(shadows),
        attrs,
        errors,
        allowSqlOnlyIntrinsics: false,
      })
    } else if (kind === "bool_query") {
      walkQuery(c.query, `constraints.${cid}.query`, {
        allowedRowFields: buildAllowedRowFields(shadows),
        attrs,
        errors,
        allowSqlOnlyIntrinsics: true,
      })

      // assert must be SQL-lowerable in v0 (rows_count + arg + boolean algebra + comparisons)
      walkExpr(c.assert, `constraints.${cid}.assert`, {
        allowedRowFields: new Set(["rows_count"]), // assert env is synthetic
        attrs: new Set(),
        errors,
        allowSqlOnlyIntrinsics: true,
        assertMode: true,
      })
    } else {
      errors.push({ code: "ILLEGAL_EXPR", path: `constraints.${cid}.kind`, message: `unknown kind '${kind}'` })
    }
  }

  if (errors.length) return { ok: false, errors, warnings }
  return { ok: true, warnings }
}

function buildAllowedRowFields (shadows: Set<string>): Set<string> {
  const s = new Set<string>(CORE_ROW_FIELDS)
  for (const k of shadows) s.add(k)
  return s
}

function walkQuery (
  q: any,
  path: string,
  ctx: WalkCtx
) {
  if (!q || typeof q !== "object") {
    ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: "query must be object" })
    return
  }
  walkSource(q.source, `${path}.source`, ctx)
  const pipeline = q.pipeline ?? []
  if (!Array.isArray(pipeline)) {
    ctx.errors.push({ code: "ILLEGAL_EXPR", path: `${path}.pipeline`, message: "pipeline must be array" })
    return
  }
  for (let i = 0; i < pipeline.length; i++) {
    const op: any = pipeline[i]
    const tag = soleKey(op)
    const body = op[tag]
    if (tag === "filter") walkExpr(body, `${path}.pipeline[${i}].filter`, ctx)
    else if (tag === "project") {
      const fields = body?.fields ?? []
      if (!Array.isArray(fields)) {
        ctx.errors.push({ code: "ILLEGAL_EXPR", path: `${path}.pipeline[${i}].project.fields`, message: "fields must be array" })
      } else {
        for (let j = 0; j < fields.length; j++) {
          walkExpr(fields[j]?.expr, `${path}.pipeline[${i}].project.fields[${j}].expr`, ctx)
        }
      }
    } else if (tag === "group_by") {
      const keys = body?.keys ?? []
      const aggs = body?.aggs ?? {}
      for (let j = 0; j < (keys.length ?? 0); j++) walkExpr(keys[j]?.expr, `${path}.pipeline[${i}].group_by.keys[${j}].expr`, ctx)
      for (const [name, agg] of Object.entries(aggs)) walkAgg(agg, `${path}.pipeline[${i}].group_by.aggs.${name}`, ctx)
    } else if (tag === "order_by") {
      const ks = body ?? []
      for (let j = 0; j < (ks.length ?? 0); j++) walkExpr(ks[j]?.expr, `${path}.pipeline[${i}].order_by[${j}].expr`, ctx)
    } else if (tag === "limit" || tag === "offset") {
      // ok
    } else {
      ctx.errors.push({ code: "ILLEGAL_EXPR", path: `${path}.pipeline[${i}]`, message: `unknown op '${tag}'` })
    }
  }
}

function walkSource (src: any, path: string, ctx: WalkCtx) {
  if (!src || typeof src !== "object") {
    ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: "source must be object" })
    return
  }
  const tag = soleKey(src)
  const body = src[tag]
  if (tag === "snap") return
  if (tag === "sla_status") return
  if (tag === "join") {
    walkSource(body?.left, `${path}.join.left`, ctx)
    walkSource(body?.right, `${path}.join.right`, ctx)
    // join fields are not typechecked in v0 (would require schema of both sides)
    return
  }
  ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: `unknown source '${tag}'` })
}

type WalkCtx = {
  allowedRowFields: Set<string>
  attrs: Set<string>
  errors: TypecheckError[]
  allowSqlOnlyIntrinsics: boolean
  assertMode?: boolean // bool_query.assert
}

function walkAgg (agg: any, path: string, ctx: WalkCtx) {
  if (!agg || typeof agg !== "object") {
    ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: "agg must be object" })
    return
  }
  const tag = soleKey(agg)
  const body = agg[tag]
  if (tag === "count") return
  if (tag === "sum" || tag === "min" || tag === "max") {
    walkExpr(body?.expr, `${path}.${tag}.expr`, ctx)
    return
  }
  ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: `unknown agg '${tag}'` })
}

function walkExpr (expr: any, path: string, ctx: WalkCtx) {
  if (expr == null) {
    ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: "expr missing" })
    return
  }
  if (typeof expr !== "object") {
    ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: "expr must be object" })
    return
  }

  const tag = soleKey(expr)
  const body = expr[tag]

  switch (tag) {
    case "lit":
      return

    case "var": {
      const vTag = soleKey(body)
      const vBody = body[vTag]

      if (vTag === "row") {
        const field = String(vBody?.field ?? "")
        if (!ctx.allowedRowFields.has(field)) {
          ctx.errors.push({
            code: "ILLEGAL_ROW_FIELD",
            path: `${path}.var.row.field`,
            message: `row field '${field}' is not core/shadow; use get(row.attrs_json, '<attr>') or declare shadow`,
          })
        }
        return
      }

      if (ctx.assertMode) {
        if (vTag === "rows_count") return
        if (vTag === "arg") return
        ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: `assert var '${vTag}' not allowed` })
        return
      }

      // allow common env vars
      if (vTag === "state" || vTag === "now" || vTag === "actor" || vTag === "input" || vTag === "attrs" || vTag === "e_payload") return

      // default: ok (v0 keeps env open for runtime)
      return
    }

    case "get": {
      // convention check: get(var.row.attrs_json, "foo") must reference declared attr
      const inner = body?.expr
      const innerTag = inner && typeof inner === "object" ? soleKey(inner) : ""
      const innerBody = innerTag ? inner[innerTag] : null

      const okBase =
        innerTag === "var" &&
        innerBody &&
        soleKey(innerBody) === "row" &&
        String(innerBody.row?.field ?? "") === "attrs_json"

      if (okBase) {
        const p = String(body?.path ?? "")
        const top = p.split(".")[0]!
        if (top && !ctx.attrs.has(top)) {
          ctx.errors.push({
            code: "UNKNOWN_ATTR",
            path: `${path}.get.path`,
            message: `attr '${top}' not declared on type (via attrs)`,
          })
        }
      }

      walkExpr(body?.expr, `${path}.get.expr`, ctx)
      return
    }

    case "has":
      walkExpr(body?.expr, `${path}.has.expr`, ctx)
      return

    case "obj":
      for (const [k, v] of Object.entries(body?.fields ?? {})) walkExpr(v, `${path}.obj.fields.${k}`, ctx)
      return

    case "arr":
      for (let i = 0; i < (body?.items ?? []).length; i++) walkExpr(body.items[i], `${path}.arr.items[${i}]`, ctx)
      return

    case "not":
      walkExpr(body, `${path}.not`, ctx)
      return

    case "bool":
      walkExpr(body, `${path}.bool`, ctx)
      return

    case "and":
    case "or":
    case "coalesce": {
      const xs = body as any[]
      for (let i = 0; i < (xs?.length ?? 0); i++) walkExpr(xs[i], `${path}.${tag}[${i}]`, ctx)
      return
    }

    case "eq":
    case "ne":
    case "lt":
    case "le":
    case "gt":
    case "ge":
    case "add":
    case "sub":
    case "mul":
    case "div":
    case "time_between": {
      const [a, b] = body as any[]
      walkExpr(a, `${path}.${tag}[0]`, ctx)
      walkExpr(b, `${path}.${tag}[1]`, ctx)
      return
    }

    case "in":
      walkExpr(body?.needle, `${path}.in.needle`, ctx)
      walkExpr(body?.haystack, `${path}.in.haystack`, ctx)
      return

    case "if":
      walkExpr(body?.cond, `${path}.if.cond`, ctx)
      walkExpr(body?.then, `${path}.if.then`, ctx)
      walkExpr(body?.else, `${path}.if.else`, ctx)
      return

    case "is_null":
      walkExpr(body, `${path}.is_null`, ctx)
      return

    case "map_enum":
      walkExpr(body?.expr, `${path}.map_enum.expr`, ctx)
      return

    case "call": {
      const fn = String(body?.fn ?? "")
      const args = body?.args ?? []
      for (let i = 0; i < (args?.length ?? 0); i++) walkExpr(args[i], `${path}.call.args[${i}]`, ctx)

      if (ctx.allowSqlOnlyIntrinsics) {
        // allowed inside SQL-lowered contexts
        if (fn === "len" || fn === "str" || fn === "int" || fn === "float") return

        // explicit disallow: policy/auth/constraint intrinsics inside views/SQL constraints
        ctx.errors.push({
          code: "ILLEGAL_INTRINSIC",
          path: `${path}.call.fn`,
          message: `intrinsic '${fn}' not allowed in SQL-lowered context`,
        })
        return
      }

      return
    }

    default:
      ctx.errors.push({ code: "ILLEGAL_EXPR", path, message: `unknown expr tag '${tag}'` })
      return
  }
}

function soleKey (o: any): string {
  const ks = Object.keys(o ?? {})
  if (ks.length !== 1) throw new Error("invalid tagged object")
  return ks[0]!
}
