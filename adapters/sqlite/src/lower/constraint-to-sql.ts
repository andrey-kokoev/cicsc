import type { BoolQueryConstraintV0, ExprV0 } from "../../../core/ir/types"
import type { SqlPlan } from "./query-to-sql"
import { lowerQueryToSql, lowerExprToSqlValue } from "./query-to-sql"

export type ConstraintSqlPlan = {
  sql: string      // returns single row { ok: 0|1 }
  binds: any[]
}

export function lowerBoolQueryConstraintToSql (params: {
  constraint: BoolQueryConstraintV0
  version: number
  tenant_id: string

  // concrete args (constraint parameterization)
  args: Record<string, any>
}): ConstraintSqlPlan {
  const { constraint, version, tenant_id, args } = params

  // 1) lower base query into a subquery "q"
  const qPlan: SqlPlan = lowerQueryToSql(constraint.query, { version, tenant_id })

  // 2) build assertion env: rows_count + (optional) agg. In v0 we only support rows_count in SQL.
  // Therefore, asserts must be representable as SQL over rows_count.
  //
  // We compute rows_count as:
  //   SELECT COUNT(1) FROM (<query sans limit/offset/order/project?>) q
  // But our query-to-sql includes project/order/limit. For constraint checking we want a stable count
  // over the full filtered set, so we wrap *that* output and count its rows.

  const countSql = `SELECT COUNT(1) AS rows_count FROM (\n${qPlan.sql}\n) q`

  // 3) lower assert expression, substituting:
  // - var.rows_count -> rows_count column
  // - var.arg.name -> binds (args[name])
  //
  // We lower assert by treating it as expression over a synthetic single-row "row" with rows_count.
  const assertBinds: any[] = []
  const assertSqlRaw = lowerAssertExpr(constraint.assert, assertBinds)

  // 4) replace __ARG__...__ sentinels with real binds
  const { sql: assertSql, binds: assertBinds2 } = replaceArgSentinels(assertSqlRaw, assertBinds, args)

  // 5) final ok query:
  // SELECT CASE WHEN (<assert>) THEN 1 ELSE 0 END AS ok FROM (countSql) row;
  const sql =
    `SELECT CASE WHEN (${assertSql}) THEN 1 ELSE 0 END AS ok\n` +
    `FROM (\n${countSql}\n) row`

  // binds:
  // - qPlan needs tenant/name/on_type binds for source (currently in query-to-sql source; but it didn't push binds)
  // We must patch that: query-to-sql source uses '?' literals but didn't add binds. Do it here for v0:
  // Snap source: [tenant_id, entity_type]
  // Sla source:  [tenant_id, name, entity_type]
  //
  // We derive binds by scanning the source. For now, handle the common case:
  const sourceBinds = inferSourceBinds(constraint.query.source, tenant_id)

  return { sql, binds: [...sourceBinds, ...qPlan.binds, ...assertBinds2] }
}

function lowerAssertExpr (expr: ExprV0, binds: any[]): string {
  // We reuse query-to-sql lowering, but we need special handling for rows_count and arg.
  // Minimal implementation: directly lower with a restricted subset.
  const tag = soleKey(expr)
  const body: any = (expr as any)[tag]

  switch (tag) {
    case "lit": {
      const lt = soleKey(body)
      const v = (body as any)[lt]
      if (lt === "null") return "NULL"
      if (lt === "bool") return v ? "1" : "0"
      if (lt === "int" || lt === "float") return typeof v === "number" ? String(v) : "NULL"
      if (lt === "string") {
        binds.push(String(v))
        return "?"
      }
      return "NULL"
    }

    case "var": {
      const vt = soleKey(body)
      const vv = (body as any)[vt]
      if (vt === "rows_count") return `row.rows_count`
      if (vt === "arg") return `__ARG__${String(vv.name)}__`
      throw new Error(`assert: unsupported var ${vt}`)
    }

    case "not":
      return `(NOT (${lowerAssertExpr(body, binds)}))`

    case "and": {
      const xs = body as ExprV0[]
      if (!xs.length) return "1"
      return `(${xs.map((e) => `(${lowerAssertExpr(e, binds)})`).join(" AND ")})`
    }

    case "or": {
      const xs = body as ExprV0[]
      if (!xs.length) return "0"
      return `(${xs.map((e) => `(${lowerAssertExpr(e, binds)})`).join(" OR ")})`
    }

    case "eq":
    case "ne":
    case "lt":
    case "le":
    case "gt":
    case "ge": {
      const [a, b] = body as [ExprV0, ExprV0]
      const la = lowerAssertExpr(a, binds)
      const lb = lowerAssertExpr(b, binds)
      const op = tag === "eq" ? "=" : tag === "ne" ? "!=" : tag === "lt" ? "<" : tag === "le" ? "<=" : tag === "gt" ? ">" : ">="
      return `(${la} ${op} ${lb})`
    }

    case "add":
    case "sub":
    case "mul":
    case "div": {
      const [a, b] = body as [ExprV0, ExprV0]
      const la = lowerAssertExpr(a, binds)
      const lb = lowerAssertExpr(b, binds)
      const op = tag === "add" ? "+" : tag === "sub" ? "-" : tag === "mul" ? "*" : "/"
      return `(${la} ${op} ${lb})`
    }

    case "if": {
      const c = lowerAssertExpr(body.cond, binds)
      const t = lowerAssertExpr(body.then, binds)
      const e = lowerAssertExpr(body.else, binds)
      return `(CASE WHEN (${c}) THEN (${t}) ELSE (${e}) END)`
    }

    case "coalesce": {
      const xs = body as ExprV0[]
      if (!xs.length) return "NULL"
      return `COALESCE(${xs.map((e) => lowerAssertExpr(e, binds)).join(", ")})`
    }

    case "is_null":
      return `(${lowerAssertExpr(body, binds)} IS NULL)`

    default:
      throw new Error(`assert: unsupported expr tag ${tag}`)
  }
}

function inferSourceBinds (src: any, tenant_id: string): any[] {
  const tag = soleKey(src)
  const body: any = (src as any)[tag]

  if (tag === "snap") return [tenant_id, String(body.type)]
  if (tag === "sla_status") return [tenant_id, String(body.name), String(body.on_type)]
  if (tag === "join") return [...inferSourceBinds(body.left, tenant_id), ...inferSourceBinds(body.right, tenant_id)]
  throw new Error(`inferSourceBinds: unsupported source tag ${tag}`)
}

function replaceArgSentinels (sql: string, binds: any[], args: Record<string, any>): { sql: string; binds: any[] } {
  // We replace tokens __ARG__name__ with ? and append bind in encountered order.
  // Also support quoted ident segments by allowing any [A-Za-z0-9_]+ in name.
  const outBinds = [...binds]
  const re = /__ARG__([A-Za-z0-9_]+)__/g

  let m: RegExpExecArray | null
  let outSql = ""
  let last = 0

  while ((m = re.exec(sql))) {
    outSql += sql.slice(last, m.index) + "?"
    const name = m[1]!
    outBinds.push(args[name] ?? null)
    last = m.index + m[0].length
  }
  outSql += sql.slice(last)

  return { sql: outSql, binds: outBinds }
}

function soleKey (o: object): string {
  const ks = Object.keys(o)
  if (ks.length !== 1) throw new Error("invalid tagged object")
  return ks[0]!
}
