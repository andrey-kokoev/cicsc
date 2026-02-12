export type SlaStore = {
  adapter: {
    sla_check_due: (params: {
      tenant_id: string
      name: string
      now: number
      limit: number
    }) => Promise<Array<{ tenant_id: string; name: string; entity_type: string; entity_id: string }>>
    sla_mark_breached: (params: {
      tenant_id: string
      name: string
      entity_type: string
      entity_id: string
      now: number
    }) => Promise<void>
  }
}

export async function runSlaEvaluationSweep (params: {
  store: SlaStore
  tenant_id: string
  sla_names: string[]
  now: number
  limit_per_sla?: number
}): Promise<{ scanned: number; marked_breached: number }> {
  const lim = Math.max(1, Math.min(params.limit_per_sla ?? 1000, 5000))
  let scanned = 0
  let marked = 0

  for (const name of params.sla_names) {
    const due = await params.store.adapter.sla_check_due({
      tenant_id: params.tenant_id,
      name,
      now: params.now,
      limit: lim,
    })
    scanned += due.length

    for (const row of due) {
      await params.store.adapter.sla_mark_breached({
        tenant_id: row.tenant_id,
        name: row.name,
        entity_type: row.entity_type,
        entity_id: row.entity_id,
        now: params.now,
      })
      marked++
    }
  }

  return { scanned, marked_breached: marked }
}
