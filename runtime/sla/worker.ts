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
    // Additional methods for breach action execution
    get_sla_spec: (params: {
      tenant_id: string
      name: string
    }) => Promise<{ enforce: any } | null> // Gets the SLA specification
  }
}

import type { CoreIrV0 } from "../../core/ir/types"

export async function runSlaEvaluationSweep (params: {
  store: SlaStore
  ir: CoreIrV0
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

      // Execute breach action if specified in the SLA spec
      const slaSpec = params.ir.slas?.[name]
      if (slaSpec) {
        await executeBreachAction({
          store: params.store,
          ir: params.ir,
          sla: slaSpec,
          tenant_id: row.tenant_id,
          entity_type: row.entity_type,
          entity_id: row.entity_id,
          now: params.now,
        })
      }
    }
  }

  return { scanned, marked_breached: marked }
}

// Helper function to execute breach actions based on SLA enforcement configuration
async function executeBreachAction(params: {
  store: SlaStore
  ir: CoreIrV0
  sla: any // SlaSpecV0
  tenant_id: string
  entity_type: string
  entity_id: string
  now: number
}) {
  const enforce = params.sla.enforce
  
  if (enforce.notify) {
    // For notify enforcement, emit the specified event
    // This would typically involve queuing an event/command to notify stakeholders
    console.log(`SLA ${params.sla.name} breached for ${params.entity_type}/${params.entity_id}, emitting notification event: ${enforce.notify.emit_event}`)
    // In a real implementation, this would queue an event or command
  } else if (enforce.auto_transition) {
    // For auto_transition enforcement, transition the entity to the specified state
    console.log(`SLA ${params.sla.name} breached for ${params.entity_type}/${params.entity_id}, transitioning to state: ${enforce.auto_transition.to_state}`)
    // In a real implementation, this would execute a command to transition the entity
  }
  // 'none' enforcement does nothing
}
