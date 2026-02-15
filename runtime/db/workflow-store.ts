// /runtime/db/workflow-store.ts

export type WorkflowStatus = 'running' | 'waiting' | 'completed' | 'failed' | 'compensated'

export interface WorkflowInstance {
  tenant_id: string
  workflow_id: string
  workflow_name: string
  current_step: string
  status: WorkflowStatus
  wait_event_type: string | null
  context_json: string
  history_json: string
  next_run_at: number | null
  created_ts: number
  updated_ts: number
}

export interface WorkflowStore {
  createInstance(instance: WorkflowInstance): Promise<void>
  updateInstance(instance: Partial<WorkflowInstance> & { tenant_id: string, workflow_id: string }): Promise<void>
  getInstance(tenant_id: string, workflow_id: string): Promise<WorkflowInstance | null>
  listDueInstances(params: { tenant_id: string, now: number }): Promise<WorkflowInstance[]>
  appendLog(entry: { tenant_id: string, workflow_id: string, step_name: string, action: string, payload_json: string, ts: number }): Promise<void>
}
