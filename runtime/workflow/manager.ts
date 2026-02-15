// /runtime/workflow/manager.ts

import type { CoreIrV0 } from "../../core/ir/types"
import type { SqliteD1Adapter } from "../../adapters/sqlite/src/adapter"

export class WorkflowManager {
  constructor(
    private ir: CoreIrV0,
    private adapter: SqliteD1Adapter
  ) { }

  async onEventsEmitted (params: {
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

  async startWorkflow (params: { tenant_id: string; workflow_name: string; input: any }): Promise<string> {
    const { tenant_id, workflow_name, input } = params
    const wf = this.ir.workflows?.[workflow_name]
    if (!wf) throw new Error(`unknown workflow: ${workflow_name}`)

    const workflow_id = `wf_${Math.random().toString(36).substring(2, 10)}`
    const now = Math.floor(Date.now() / 1000)
    await this.adapter.create_workflow_instance({
      tenant_id,
      workflow_id,
      workflow_name,
      current_step: wf.initial_step,
      status: "running",
      wait_event_type: null,
      context_json: JSON.stringify({ manual_start: true, input }),
      history_json: "[]",
      next_run_at: null,
      created_ts: now,
      updated_ts: now,
    })
    return workflow_id
  }

  async getWorkflowStatus (tenant_id: string, workflow_id: string) {
    return this.adapter.get_workflow_instance(tenant_id, workflow_id)
  }

  async cancelWorkflow (tenant_id: string, workflow_id: string) {
    const now = Math.floor(Date.now() / 1000)
    await this.adapter.update_workflow_instance({
      tenant_id,
      workflow_id,
      status: "failed",
      updated_ts: now,
    })
  }

  async listStuckWorkflows (params: { tenant_id: string; older_than_seconds: number; now: number }) {
    // Workflows in 'running' status for too long
    const threshold = params.now - params.older_than_seconds
    // Simplified query using adapter's existing capabilities or raw query if needed.
    // I'll add a method to adapter.
    return (this.adapter as any).list_stuck_workflow_instances({
      tenant_id: params.tenant_id,
      threshold,
    })
  }
}
