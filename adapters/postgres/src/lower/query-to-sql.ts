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
  sql = sql.replace(/\battrs_json\b/g, "attrs")

  return { sql, binds: plan.binds }
}
