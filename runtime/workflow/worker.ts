// /runtime/workflow/worker.ts

import type { CoreIrV0, WorkflowStepV0 } from "../../core/ir/types"
import type { WorkflowStore, WorkflowInstance } from "../db/workflow-store"
import { evalExpr, type VmEnv, type VmIntrinsics } from "../../core/vm/eval"

export class WorkflowWorker {
  constructor(
    private ir: CoreIrV0,
    private store: WorkflowStore,
    private intrinsics: VmIntrinsics,
    private runCommand: (tenant_id: string, entity_type: string, entity_id: string, command: string, input: any) => Promise<any>
  ) {}

  async pollAndExecute(tenant_id: string, params: { now: number }) {
    const { now } = params
    const instances = await this.store.listDueInstances({ tenant_id, now })
    let processed = 0
    let errors = 0

    for (const inst of instances) {
      try {
        await this.processInstance(inst, now)
        processed++
      } catch (e) {
        console.error(`Error processing workflow instance ${inst.workflow_id}:`, e)
        errors++
      }
    }
    return { processed, errors }
  }

  private async processInstance(inst: WorkflowInstance, now: number) {
    const wf = this.ir.workflows?.[inst.workflow_name]
    if (!wf) {
       await this.store.updateInstance({ tenant_id: inst.tenant_id, workflow_id: inst.workflow_id, status: 'failed', updated_ts: now })
       return
    }

    const context = inst.context_json ? JSON.parse(inst.context_json) : {}
    const history = inst.history_json ? JSON.parse(inst.history_json) : []

    let currentStepName = inst.current_step
    let status = inst.status

    while (status === 'running') {
      const step = wf.steps[currentStepName]
      if (!step) {
          status = 'failed'
          break
      }

      const result = await this.executeStep(inst.tenant_id, inst.workflow_id, currentStepName, step, context, now)
      
      history.push({ step: currentStepName, action: result.action, outcome: result.outcome, ts: now })
      await this.store.appendLog({
          tenant_id: inst.tenant_id,
          workflow_id: inst.workflow_id,
          step_name: currentStepName,
          action: result.action,
          payload_json: JSON.stringify(result.outcome || {}),
          ts: now
      })

      if (result.action === 'wait') {
          status = 'waiting'
          await this.store.updateInstance({
              tenant_id: inst.tenant_id,
              workflow_id: inst.workflow_id,
              status,
              next_run_at: result.wait_until || null,
              history_json: JSON.stringify(history),
              updated_ts: now
          })
          return
      }

      if (result.action === 'end') {
          status = 'completed'
          break
      }

      if (result.action === 'fail') {
          status = 'failed'
          break
      }

      if (result.action === 'next') {
          currentStepName = result.next_step!
          // Auto-save progress
          await this.store.updateInstance({
              tenant_id: inst.tenant_id,
              workflow_id: inst.workflow_id,
              current_step: currentStepName,
              status,
              context_json: JSON.stringify(context),
              history_json: JSON.stringify(history),
              updated_ts: now
          })
      }
    }

    // Final update if state changed to completed/failed
    if (status !== 'running') {
        await this.store.updateInstance({
            tenant_id: inst.tenant_id,
            workflow_id: inst.workflow_id,
            status,
            history_json: JSON.stringify(history),
            updated_ts: now
        })
    }
  }

  private async executeStep(
    tenant_id: string, 
    workflow_id: string, 
    stepName: string, 
    step: WorkflowStepV0, 
    context: any, 
    now: number
  ): Promise<{ action: 'next' | 'wait' | 'end' | 'fail', next_step?: string, wait_until?: number, outcome?: any }> {
      switch (step.kind) {
          case 'end':
              return { action: 'end' }

          case 'command': {
              const env: VmEnv = {
                  now,
                  actor: `workflow:${workflow_id}`,
                  state: 'workflow_running',
                  input: {},
                  attrs: {},
                  row: {},
                  arg: context,
                  intrinsics: this.intrinsics
              }
              const input: any = {}
              for (const [k, ex] of Object.entries(step.input_map)) {
                  input[k] = evalExpr(ex, env)
              }

              try {
                  const entity_id = input.entity_id || workflow_id
                  const outcome = await this.runCommand(tenant_id, step.entity_type, entity_id, step.command, input)
                  context[stepName] = outcome 
                  return { action: 'next', next_step: step.next || 'end', outcome }
              } catch (e: any) {
                  return { action: 'fail', outcome: { error: e.message } }
              }
          }

          case 'wait': {
              // Check if we already waited long enough if it's a timeout
              const waitStep = step as any
              if (waitStep.timeout_seconds) {
                  // If we are processign this step, we just started it or it's a timeout poll.
                  // For v1, wait steps are transitioned to 'waiting' state.
                  // The polling logic for 'waiting' instances will pick it up after next_run_at.
                  return { action: 'wait', wait_until: now + waitStep.timeout_seconds }
              }
              return { action: 'wait', wait_until: undefined }
          }

          case 'decision': {
              const env: VmEnv = {
                  now,
                  actor: `workflow:${workflow_id}`,
                  state: 'workflow_running',
                  input: {},
                  attrs: {},
                  row: {},
                  arg: context,
                  intrinsics: this.intrinsics
              }
              for (const c of step.cases) {
                  if (toBool(evalExpr(c.condition, env))) {
                      return { action: 'next', next_step: c.next }
                  }
              }
              return { action: 'next', next_step: step.default_next }
          }

          default:
              return { action: 'fail', outcome: { error: `Unknown step kind: ${(step as any).kind}` } }
      }
  }
}

function toBool(v: any): boolean {
    if (typeof v === 'boolean') return v
    if (v === null || v === undefined) return false
    return !!v
}
