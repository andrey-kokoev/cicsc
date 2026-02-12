import type { CoreIrV0 } from "../../core/ir/types"
import type { AuditRecord } from "./export"

export function makePolicyChangeAuditRecords (params: {
  tenant_id: string
  actor_id: string
  ts: number
  before?: CoreIrV0
  after: CoreIrV0
}): AuditRecord[] {
  const out: AuditRecord[] = []
  const before = params.before?.policies ?? {}
  const after = params.after.policies ?? {}
  const keys = new Set<string>([...Object.keys(before), ...Object.keys(after)])

  for (const k of Array.from(keys).sort()) {
    const a = (after as any)[k]
    const b = (before as any)[k]
    if (a == null && b == null) continue

    const beforeJson = b == null ? null : JSON.stringify(b)
    const afterJson = a == null ? null : JSON.stringify(a)
    if (beforeJson === afterJson) continue

    const action = b == null ? "policy_added" : a == null ? "policy_removed" : "policy_updated"
    out.push({
      ts: params.ts,
      tenant_id: params.tenant_id,
      kind: "policy",
      payload: {
        action,
        policy: k,
        actor_id: params.actor_id,
        before: b ?? null,
        after: a ?? null,
      },
    })
  }

  return out
}
