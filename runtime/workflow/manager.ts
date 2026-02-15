// /runtime/workflow/manager.ts

import type { CoreIrV0 } from "../../core/ir/types"
import type { SqliteD1Adapter } from "../../adapters/sqlite/src/adapter"

export class WorkflowManager {
  constructor(
    private ir: CoreIrV0,
    private adapter: SqliteD1Adapter
  ) {}

  async onEventsEmitted(params: {
    tenant_id: string
    entity_type: string
    entity_id: string
    events: { event_type: string; payload: any; ts: number; actor_id: string }[]
  }) {
    const { tenant_id, events } = params
    for (const e of events) {
      // 1. Start new workflows triggered by this event
      for (const [wfName, wfSpec] of Object.entries(this.ir.workflows ?? {})) {
        if (wfSpec.on_event === e.event_type) {
          const workflow_id = `wf_${Math.random().toString(36).substring(2, 10)}`
          await this.adapter.create_workflow_instance({
            tenant_id,
            workflow_id,
            workflow_name: wfName,
            current_step: wfSpec.initial_step,
            status: 'running',
            wait_event_type: null,
            context_json: JSON.stringify({ trigger_event: e }),
            history_json: '[]',
            next_run_at: null,
            created_ts: e.ts,
            updated_ts: e.ts
          })
        }
      }

      // 2. Wake up waiting workflows
      const waiting = await this.adapter.list_workflow_instances_waiting_for_event({ tenant_id, event_type: e.event_type })
      for (const inst of waiting) {
        const wf = this.ir.workflows?.[inst.workflow_name]
        const step = wf?.steps[inst.current_step]
        if (step?.kind === 'wait' && step.event_type === e.event_type) {
           const context = JSON.parse(inst.context_json)
           context[inst.current_step] = e.payload
           await this.adapter.update_workflow_instance({
             tenant_id,
             workflow_id: inst.workflow_id,
             status: 'running',
             current_step: step.next,
             wait_event_type: null,
             context_json: JSON.stringify(context),
             updated_ts: e.ts
           })
        }
      }
    }
  }
}
