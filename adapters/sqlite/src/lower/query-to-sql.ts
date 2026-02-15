// /adapters/sqlite/src/lower/query-to-sql.ts

import type { AggExprV0, ExprV0, OpV0, QueryV0, SourceV0 } from "../../../../core/ir/types"

const PHASE9_SQL_HAVING_ENABLED = true
const PHASE9_SQL_EXISTS_ENABLED = false

export type SqlPlan = {
  sql: string
  binds: any[]
}

export type LoweringCtx = {
  version: number // events_v{v}, snapshots_v{v}
  tenant_id: string
  actor_id?: string // for RLS enforcement (BT2.4)

  // In v0 we assume snapshots are stored flat as:
  //   snapshots_vX: tenant_id, entity_type, entity_id, state, attrs_json, updated_ts, + shadow columns
  // Query rows expose fields via:
  //   row.entity_id -> entity_id
  //   row.state     -> state
  //   row.updated_ts-> updated_ts
  //   row.<shadow>  -> column (if exists)
  //   row.<attr>    -> json_extract(attrs_json, '$.<attr>')  (limited)
  // and in join:
  //   left.<field>, right.<field>
}

export function lowerQueryToSql (q: QueryV0, ctx: LoweringCtx, rowPolicy?: any): SqlPlan {
  const binds: any[] = []

  const from = lowerSource(q.source, ctx, rowPolicy)
  
  // Add any RLS binds from the source
  if (from.binds) {
    binds.push(...from.binds)
  }

  // pipeline lowering: fold into WHERE / SELECT / GROUP BY / ORDER / LIMIT/OFFSET
  let where: string[] = []
  let having: string[] = []
  let select: string[] | null = null
  let groupBy: string[] | null = null
  let orderBy: string[] | null = null
  let limit: number | null = null
  let offset: number | null = null

  // for GROUP BY we must retain projected keys and agg aliases
  let aggSelect: string[] | null = null
  let projectedAliases: Set<string> = new Set()

  for (const op of q.pipeline) {
    const tag = soleKey(op)
    const body: any = (op as any)[tag]

    switch (tag) {
      case "filter": {
        const { sql, binds: b } = lowerExprToSqlBool(body as ExprV0, ctx, "row")
        where.push(sql)
        binds.push(...b)
        break
      }

      case "project": {
        const fields = body.fields as { name: string; expr: ExprV0 }[]
        projectedAliases = new Set(fields.map((f) => f.name))
        select = fields.map((f) => {
          const { sql, binds: b } = lowerExprToSqlValue(f.expr, ctx, "row")
          binds.push(...b)
          return `${sql} AS ${escapeIdent(f.name)}`
        })
        break
      }

      case "group_by": {
        const keys = body.keys as { name: string; expr: ExprV0 }[]
        const aggs = body.aggs as Record<string, AggExprV0>

        const keySelect = keys.map((k) => {
          const { sql, binds: b } = lowerExprToSqlValue(k.expr, ctx, "row")
          binds.push(...b)
          return `${sql} AS ${escapeIdent(k.name)}`
        })
        const keyCols = keys.map((k) => escapeIdent(k.name))

        const aggParts: string[] = []
        for (const [name, agg] of Object.entries(aggs)) {
          aggParts.push(`${lowerAggToSql(agg, ctx, "row", binds)} AS ${escapeIdent(name)}`)
        }

        // After GROUP BY, the row namespace becomes the grouped row; project/order refer to aliases.
        select = [...keySelect, ...aggParts]
        groupBy = keySelect.map((s) => s.split(" AS ")[0]!.trim()) // expressions, not aliases
        aggSelect = [...keyCols, ...Object.keys(aggs).map((n) => escapeIdent(n))]
        projectedAliases = new Set([
          ...keys.map((k) => k.name),
          ...Object.keys(aggs),
        ])

        break
      }

      case "order_by": {
        const keys = body as { expr: ExprV0; dir: "asc" | "desc" }[]
        orderBy = keys.map((k) => {
          const rowField = asRowFieldRef(k.expr)
          if (rowField && projectedAliases.has(rowField)) {
            return `${escapeIdent(rowField)} ${k.dir.toUpperCase()} NULLS ${k.dir === "asc" ? "FIRST" : "LAST"}`
          }
          const lowered = lowerExprToSqlValue(k.expr, ctx, "row")
          binds.push(...lowered.binds)
          return `${lowered.sql} ${k.dir.toUpperCase()} NULLS ${k.dir === "asc" ? "FIRST" : "LAST"}`
        })
        break
      }

      case "limit":
        limit = clampInt(body as number, 0, 1_000_000)
        break

      case "offset":
        offset = clampInt(body as number, 0, 1_000_000)
        break

      case "having":
        if (!PHASE9_SQL_HAVING_ENABLED) {
          throw new Error("query op 'having' is disabled by feature gate 'phase9.sql.having'")
        }
        if (!groupBy) {
          throw new Error("query op 'having' requires a preceding group_by")
        }
        {
          const h = lowerExprToSqlValue(body as ExprV0, ctx, "group")
          binds.push(...h.binds)
          having.push(`(${h.sql})`)
        }
        break

      default:
        throw new Error(`lowerQueryToSql: unsupported op '${tag}'`)
    }
  }

  // If group_by happened, enforce SELECT shape as aliases and allow further project/order to reference them.
  // v0 simplification: we do not support a second project after group_by in SQL lowering; enforce upstream.
  if (aggSelect && select && select.some((s) => /AS\s+/i.test(s) === false)) {
    // no-op: our group_by always uses AS
  }

  const sql =
    `SELECT ${select ? select.join(", ") : "*"}\n` +
    `FROM ${from.sql}\n` +
    (where.length ? `WHERE ${where.map((w) => `(${w})`).join(" AND ")}\n` : "") +
    (groupBy ? `GROUP BY ${groupBy.join(", ")}\n` : "") +
    (having.length ? `HAVING ${having.map((h) => `(${h})`).join(" AND ")}\n` : "") +
    (orderBy ? `ORDER BY ${orderBy.join(", ")}\n` : "") +
    (limit != null ? `LIMIT ${limit}\n` : "") +
    (offset != null ? `OFFSET ${offset}\n` : "")

  return { sql, binds }
}

function lowerSource (src: SourceV0, ctx: LoweringCtx, rowPolicy?: any): { sql: string; binds?: any[] } {
  const tag = soleKey(src)
  const body: any = (src as any)[tag]

  switch (tag) {
    case "snap": {
      const t = body.type as string
      const table = `snapshots_v${ctx.version}`
      
      // Build base SQL
      let sql =
        `(SELECT *\n` +
        ` FROM ${table}\n` +
        ` WHERE tenant_id=? AND entity_type=?`
      
      // Apply RLS if provided and actor_id is in context (BT2.4)
      if (rowPolicy && ctx.actor_id) {
        const rls = lowerRowPolicyToSql(rowPolicy, ctx)
        if (rls.sql) {
          sql += ` AND ${rls.sql}`
          return { sql: sql + `) AS row`, binds: rls.binds }
        }
      }
      
      return { sql: sql + `) AS row` }
    }

    case "sla_status": {
      // sla_status not versioned; filter by tenant and name + on_type
      return {
        sql:
          `(SELECT *\n` +
          ` FROM sla_status\n` +
          ` WHERE tenant_id=? AND name=? AND entity_type=?) AS row`,
      }
    }

    case "join": {
      // v0 join is only intended for (snap join sla_status) or similar.
      const left = lowerSource(body.left, ctx)
      const right = lowerSource(body.right, ctx)
      const lf = String(body.on.left_field)
      const rf = String(body.on.right_field)
      const rightTag = soleKey(body.right)
      const leftTag = soleKey(body.left)

      // Keep unqualified keys left-biased to match oracle namespaceRow behavior.
      // For snap × sla_status we explicitly project right columns excluding entity_id
      // to avoid duplicate unqualified entity_id ambiguity in strict SQL backends.
      const joinSelect =
        leftTag === "snap" && rightTag === "sla_status"
          ? `left_.*, right_.breached, right_.deadline_ts, right_.start_ts, right_.stop_ts, right_.updated_ts, right_.entity_id AS "right.entity_id"`
          : `left_.*, right_.*`

      return {
        sql:
          `(\n` +
          `  SELECT ${joinSelect}\n` +
          `  FROM ${left.sql.replace(" AS row", " AS left_")}\n` +
          `  JOIN ${right.sql.replace(" AS row", " AS right_")}\n` +
          `    ON left_.${escapeIdent(lf)} = right_.${escapeIdent(rf)}\n` +
          `) AS row`,
      }
    }

    default:
      throw new Error(`lowerSource: unsupported tag ${tag}`)
  }
}

// --------------------------
// Expr → SQL (D1/SQLite)
// --------------------------

export function lowerExprToSqlBool (expr: ExprV0, ctx: LoweringCtx, rowAlias: string): SqlPlan {
  const p = lowerExprToSqlValue(expr, ctx, rowAlias)
  return { sql: `CASE WHEN (${p.sql}) THEN 1 ELSE 0 END`, binds: p.binds }
}

export function lowerExprToSqlValue (expr: ExprV0, ctx: LoweringCtx, rowAlias: string): SqlPlan {
  const binds: any[] = []
  const sql = lowerExpr(expr, ctx, rowAlias, binds)
  return { sql, binds }
}

function lowerExpr (expr: ExprV0, ctx: LoweringCtx, rowAlias: string, binds: any[]): string {
  const tag = soleKey(expr)
  const body: any = (expr as any)[tag]

  switch (tag) {
    case "lit":
      return lowerLit(body, binds)

    case "var":
      return lowerVar(body, ctx, rowAlias)

    case "get": {
      // JSON path from expr, only supports get(row.attrs_json, 'a.b') patterns through var+get in IR.
      const base = lowerExpr(body.expr, ctx, rowAlias, binds)
      const path = String(body.path)
      // If base is attrs_json or payload_json, we use json_extract
      // v0: assume base already yields JSON text; SQLite json_extract can operate on JSON text.
      binds.push(`$.${path}`)
      return `json_extract(${base}, ?)`
    }

    case "has": {
      const base = lowerExpr(body.expr, ctx, rowAlias, binds)
      const path = String(body.path)
      binds.push(`$.${path}`)
      return `json_type(json_extract(${base}, ?)) IS NOT NULL`
    }

    case "obj": {
      // Build JSON object as text. Use json_object with stable order.
      const fields = body.fields as Record<string, ExprV0>
      const keys = Object.keys(fields).sort()
      const parts: string[] = []
      for (const k of keys) {
        parts.push(`'${escapeSqlString(k)}'`)
        parts.push(lowerExpr(fields[k]!, ctx, rowAlias, binds))
      }
      return `json_object(${parts.join(", ")})`
    }

    case "arr": {
      // json_array(...)
      const items = body.items as ExprV0[]
      const parts = items.map((e: ExprV0) => lowerExpr(e, ctx, rowAlias, binds))
      return `json_array(${parts.join(", ")})`
    }

    case "not":
      return `(NOT (${lowerExpr(body, ctx, rowAlias, binds)}))`

    case "bool":
      return `(CASE WHEN (${lowerExpr(body, ctx, rowAlias, binds)}) THEN 1 ELSE 0 END)`

    case "and": {
      const items = body as ExprV0[]
      if (!items.length) return "1"
      return `(${items.map((e) => `(${lowerExpr(e, ctx, rowAlias, binds)})`).join(" AND ")})`
    }

    case "or": {
      const items = body as ExprV0[]
      if (!items.length) return "0"
      return `(${items.map((e) => `(${lowerExpr(e, ctx, rowAlias, binds)})`).join(" OR ")})`
    }

    case "eq":
    case "ne":
    case "lt":
    case "le":
    case "gt":
    case "ge": {
      const [a, b] = body as [ExprV0, ExprV0]
      const la = lowerExpr(a, ctx, rowAlias, binds)
      const lb = lowerExpr(b, ctx, rowAlias, binds)
      const op = tag === "eq" ? "=" : tag === "ne" ? "!=" : tag === "lt" ? "<" : tag === "le" ? "<=" : tag === "gt" ? ">" : ">="
      return `(${la} ${op} ${lb})`
    }

    case "in": {
      const needle = lowerExpr(body.needle, ctx, rowAlias, binds)
      const hay = lowerExpr(body.haystack, ctx, rowAlias, binds)
      // v0: haystack is JSON array; use json_each
      return `EXISTS (SELECT 1 FROM json_each(${hay}) WHERE value = ${needle})`
    }

    case "add":
    case "sub":
    case "mul":
    case "div": {
      const [a, b] = body as [ExprV0, ExprV0]
      const la = lowerExpr(a, ctx, rowAlias, binds)
      const lb = lowerExpr(b, ctx, rowAlias, binds)
      const op = tag === "add" ? "+" : tag === "sub" ? "-" : tag === "mul" ? "*" : "/"
      // div-by-zero behavior: SQLite returns NULL; matches oracle (null).
      return `(${la} ${op} ${lb})`
    }

    case "if": {
      const c = lowerExpr(body.cond, ctx, rowAlias, binds)
      const t = lowerExpr(body.then, ctx, rowAlias, binds)
      const e = lowerExpr(body.else, ctx, rowAlias, binds)
      return `(CASE WHEN (${c}) THEN (${t}) ELSE (${e}) END)`
    }

    case "coalesce": {
      const items = body as ExprV0[]
      if (!items.length) return "NULL"
      return `COALESCE(${items.map((e) => lowerExpr(e, ctx, rowAlias, binds)).join(", ")})`
    }

    case "is_null":
      return `(${lowerExpr(body, ctx, rowAlias, binds)} IS NULL)`

    case "time_between": {
      const [a, b] = body as [ExprV0, ExprV0]
      const la = lowerExpr(a, ctx, rowAlias, binds)
      const lb = lowerExpr(b, ctx, rowAlias, binds)
      return `(CAST(${lb} AS INTEGER) - CAST(${la} AS INTEGER))`
    }

    case "map_enum": {
      // map_enum is compiled to CASE
      const v = lowerExpr(body.expr, ctx, rowAlias, binds)
      const mapping = body.mapping as Record<string, number>
      const keys = Object.keys(mapping).sort()
      const parts = keys.map((k) => `WHEN ${v} = '${escapeSqlString(k)}' THEN ${Number(mapping[k])}`)
      return `(CASE ${parts.join(" ")} ELSE NULL END)`
    }

    case "call":
      // v0 SQL lowering only supports len/str/int/float as local, and forbids policy/constraint calls.
      // Those must be handled as snapshot-vm constraints or pushed up (guard path).
      return lowerCallSql(body.fn as string, body.args as ExprV0[], ctx, rowAlias, binds)

    case "exists":
      if (!PHASE9_SQL_EXISTS_ENABLED) {
        throw new Error("expr 'exists' is disabled by feature gate 'phase9.sql.exists'")
      }
      throw new Error("expr 'exists' lowering is not implemented")

    default:
      throw new Error(`lowerExpr: unsupported expr tag ${tag}`)
  }
}

function lowerCallSql (fn: string, args: ExprV0[], ctx: LoweringCtx, rowAlias: string, binds: any[]): string {
  switch (fn) {
    case "len": {
      const v = lowerExpr(args[0]!, ctx, rowAlias, binds)
      return `(CASE WHEN json_type(${v})='array' THEN json_array_length(${v}) ELSE LENGTH(CAST(${v} AS TEXT)) END)`
    }
    case "str": {
      const v = lowerExpr(args[0]!, ctx, rowAlias, binds)
      return `CAST(${v} AS TEXT)`
    }
    case "int": {
      const v = lowerExpr(args[0]!, ctx, rowAlias, binds)
      return `CAST(${v} AS INTEGER)`
    }
    case "float": {
      const v = lowerExpr(args[0]!, ctx, rowAlias, binds)
      return `CAST(${v} AS REAL)`
    }
    default:
      throw new Error(`lowerCallSql: unsupported intrinsic in SQL context: ${fn}`)
  }
}

function lowerAggToSql (agg: AggExprV0, ctx: LoweringCtx, rowAlias: string, binds: any[]): string {
  const tag = soleKey(agg)
  const body: any = (agg as any)[tag]

  switch (tag) {
    case "count":
      return `COUNT(1)`
    case "sum":
      return `SUM(${lowerExpr(body.expr, ctx, rowAlias, binds)})`
    case "min":
      return `MIN(${lowerExpr(body.expr, ctx, rowAlias, binds)})`
    case "max":
      return `MAX(${lowerExpr(body.expr, ctx, rowAlias, binds)})`
    case "rate": {
      const numSql = lowerExpr(body.numerator, ctx, rowAlias, binds)
      const denSql = lowerExpr(body.denominator, ctx, rowAlias, binds)
      const multiplier: Record<string, number> = {
        per_second: 1,
        per_minute: 60,
        per_hour: 3600,
        per_day: 86400,
      }
      const m = multiplier[body.unit] ?? 1
      return `CASE WHEN SUM(${denSql}) = 0 THEN NULL ELSE (SUM(${numSql}) * ${m}) / SUM(${denSql}) END`
    }
    case "ratio": {
      const numSql = lowerExpr(body.numerator, ctx, rowAlias, binds)
      const denSql = lowerExpr(body.denominator, ctx, rowAlias, binds)
      const scale = body.scale ?? 1
      return `CASE WHEN SUM(${denSql}) = 0 THEN NULL ELSE (SUM(${numSql}) * ${scale}) / SUM(${denSql}) END`
    }
    case "time_between": {
      const startSql = lowerExpr(body.start_expr, ctx, rowAlias, binds)
      const endSql = lowerExpr(body.end_expr, ctx, rowAlias, binds)
      const divisor: Record<string, number> = {
        seconds: 1,
        minutes: 60,
        hours: 3600,
        days: 86400,
      }
      const d = divisor[body.unit ?? "seconds"] ?? 1
      return `AVG((${endSql} - ${startSql}) / ${d})`
    }
    default:
      throw new Error(`lowerAggToSql: unsupported agg tag ${tag}`)
  }
}

function lowerVar (v: any, ctx: LoweringCtx, rowAlias: string): string {
  const tag = soleKey(v)
  const body: any = (v as any)[tag]

  // NOTE: in SQL context, var.row.field maps to columns on the materialized row.
  // For snapshots: prefer column if present; otherwise json_extract(attrs_json,'$.field').
  if (tag === "row") {
    const f = String(body.field)

    // Grouped row context exposes aliases directly (state, agg names).
    if (rowAlias === "group") return `${escapeIdent(f)}`

    // core columns
    if (f === "entity_id" || f === "state" || f === "updated_ts") return `${rowAlias}.${escapeIdent(f)}`

    // If field looks namespaced (left.x/right.x) it is already a column in join output
    if (f.includes(".")) return `${rowAlias}.${escapeIdent(f)}`

    // Try as direct column first; if missing, SQLite returns NULL if column doesn't exist? (it errors)
    // So: we must choose one strategy. v0 strategy:
    // - assume all non-core fields used in SQL lowering are SHADOW columns.
    // - attributes accessed from rows MUST be expressed as get(var.row.attrs_json, 'field') in IR.
    //
    // Therefore, bare row.field is treated as a physical column.
    return `${rowAlias}.${escapeIdent(f)}`
  }

  if (tag === "arg") {
    // Constraint args are bound externally; represent as a SQL bind.
    // v0: treat arg.name as a placeholder to be substituted by compiler later.
    // Here we emit a sentinel token.
    return `__ARG__${escapeIdent(String(body.name))}__`
  }

  if (tag === "rows_count") return `${rowAlias}.rows_count` // only valid after group_by via project aliasing (rare in SQL)
  if (tag === "now") return `strftime('%s','now')` // compilation should pass actual now; but keep deterministic for tests? use bind instead upstream.
  if (tag === "state") return `${rowAlias}.state`

  throw new Error(`lowerVar: unsupported var in SQL context: ${tag}`)
}

function lowerLit (lit: any, binds: any[]): string {
  const tag = soleKey(lit)
  const body: any = (lit as any)[tag]

  switch (tag) {
    case "null":
      return "NULL"
    case "bool":
      return body ? "1" : "0"
    case "int":
    case "float":
      if (typeof body !== "number") return "NULL"
      return String(body)
    case "string":
      if (typeof body !== "string") return "NULL"
      binds.push(body)
      return "?"
    default:
      return "NULL"
  }
}

function asRowFieldRef (expr: ExprV0): string | null {
  const tag = soleKey(expr)
  if (tag !== "var") return null
  const body: any = (expr as any)[tag]
  const vtag = soleKey(body)
  if (vtag !== "row") return null
  return String(body.row?.field ?? body.field ?? "")
}

function soleKey (o: object): string {
  const ks = Object.keys(o)
  if (ks.length !== 1) throw new Error("invalid tagged object")
  return ks[0]!
}

function escapeIdent (name: string): string {
  if (!/^[A-Za-z_][A-Za-z0-9_\.]*$/.test(name)) throw new Error(`invalid ident: ${name}`)
  // allow dotted names for join output; quote each segment
  return name
    .split(".")
    .map((seg) => `"${seg}"`)
    .join(".")
}

function escapeSqlString (s: string): string {
  return s.replaceAll("'", "''")
}

function clampInt (n: number, lo: number, hi: number): number {
  if (!Number.isFinite(n)) return lo
  const x = Math.trunc(n)
  return Math.min(hi, Math.max(lo, x))
}

// Row-Level Security SQL generation (BT2.4)
export function lowerRowPolicyToSql (policy: any, ctx: LoweringCtx): { sql: string; binds: any[] } {
  if (!policy || !ctx.actor_id) {
    return { sql: "", binds: [] }
  }

  const tag = soleKey(policy)
  const body = policy[tag]

  switch (tag) {
    case "owner": {
      // row.actor_field = actor_id
      return {
        sql: `${escapeIdent(body.actor_field)} = ?`,
        binds: [ctx.actor_id],
      }
    }
    case "member_of": {
      // row.target_field IN (SELECT target_field FROM memberships WHERE actor_id = ctx.actor_id AND target_type = body.target_type)
      return {
        sql: `${escapeIdent(body.target_field)} IN (SELECT target_id FROM rls_memberships WHERE actor_id = ? AND target_type = ?)`,
        binds: [ctx.actor_id, body.target_type],
      }
    }
    case "expr": {
      // Custom expression - would need full expression lowering with actor context
      // For now, return empty to allow fallback behavior
      return { sql: "", binds: [] }
    }
    default:
      return { sql: "", binds: [] }
  }
}

// Apply RLS to a snap source SQL
export function applyRlsToSnapSql (baseSql: string, policy: any, ctx: LoweringCtx): { sql: string; binds: any[] } {
  const rls = lowerRowPolicyToSql(policy, ctx)
  if (!rls.sql) {
    return { sql: baseSql, binds: [] }
  }

  // Inject RLS clause before the closing ) AS row
  const modifiedSql = baseSql.replace(/\) AS row$/, ` AND ${rls.sql}) AS row`)
  return { sql: modifiedSql, binds: rls.binds }
}
