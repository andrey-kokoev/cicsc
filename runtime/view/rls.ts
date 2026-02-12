import type { ExprV0 } from "../../core/ir/types"
import { evalExpr, type VmIntrinsics } from "../../core/vm/eval"

export function applyRowLevelSecurity (params: {
  rows: any[]
  actor_id: string
  row_policy: ExprV0
  intrinsics: VmIntrinsics
}): any[] {
  const out: any[] = []
  for (const row of params.rows) {
    const ok = evalExpr(params.row_policy, {
      now: Math.floor(Date.now() / 1000),
      actor: params.actor_id,
      state: String(row?.state ?? ""),
      input: {},
      attrs: {},
      row: row ?? {},
      arg: {},
      intrinsics: params.intrinsics,
    })
    if (ok === true) out.push(row)
  }
  return out
}
