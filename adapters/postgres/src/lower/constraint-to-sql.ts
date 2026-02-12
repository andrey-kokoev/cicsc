import type { BoolQueryConstraintV0 } from "../../../../core/ir/types"
import { lowerBoolQueryConstraintToSql as lowerSqliteConstraintToSql } from "../../../sqlite/src/lower/constraint-to-sql"

export type SqlPlan = {
  sql: string
  binds: any[]
}

export function lowerBoolQueryConstraintToSql (params: {
  constraint: BoolQueryConstraintV0
  version: number
  tenant_id: string
  args: Record<string, any>
}): SqlPlan {
  const plan = lowerSqliteConstraintToSql({
    constraint: params.constraint as any,
    version: params.version,
    tenant_id: params.tenant_id,
    args: params.args,
  })
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
