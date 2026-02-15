import type { QueryV0 } from "../../../../core/ir/types"
import { lowerQueryToSql as lowerSqliteQueryToSql } from "../../../sqlite/src/lower/query-to-sql"

export type SqlPlan = {
  sql: string
  binds: any[]
}

export function lowerQueryToSql (q: QueryV0, params: { version: number; tenant_id: string }): SqlPlan {
  const plan = lowerSqliteQueryToSql(q as any, { version: params.version, tenant_id: params.tenant_id } as any)
  return toPostgresPlan(plan)
}

function toPostgresPlan (plan: SqlPlan): SqlPlan {
  let n = 0
  let sql = plan.sql.replace(/\?/g, () => `$${++n}`)

  // Dialect differences
  sql = sql.replace(/strftime\('%s','now'\)/g, "EXTRACT(EPOCH FROM NOW())::bigint")
  sql = sql.replace(/\bjson_extract\b\((attrs_json),\s*'(.+?)'\)/g, "$1->>$2")
  sql = sql.replace(/\battrs_json\b/g, "attrs_json")
  
  // SQLite lowering emits numeric-boolean CASE wrappers in WHERE clauses.
  // Postgres expects boolean WHERE predicates.
  sql = sql.replace(/WHERE\s+\(CASE WHEN \(([\s\S]*?)\) THEN 1 ELSE 0 END = 1\)/g, "WHERE $1")
  
  // Handle bool literals
  sql = sql.replace(/=\s*0\b/g, "= FALSE")
  sql = sql.replace(/=\s*1\b/g, "= TRUE")

  // For window functions (BE2.4)
  // v0: If we see a pattern that looks like a cumulative sum or rank in the pipeline
  // we would emit standard Postgres window SQL.
  
  return { sql, binds: plan.binds }
}
