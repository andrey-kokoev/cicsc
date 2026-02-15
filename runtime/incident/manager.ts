import { IR } from "../../core/ir/types.js";

export interface Incident {
  id: string;
  tenant_id: string;
  source_type: "workflow" | "schedule";
  source_id: string;
  incident_type: string;
  message: string;
  status: "open" | "resolved" | "ignored";
  context_json: string;
  created_ts: number;
}

export interface IncidentStore {
  create_incident(incident: Omit<Incident, "id">): Promise<string>;
  get_incident(tenant_id: string, id: string): Promise<Incident | null>;
  list_incidents(tenant_id: string, status?: string): Promise<Incident[]>;
  resolve_incident(tenant_id: string, id: string): Promise<void>;
}

export class IncidentManager {
  constructor(
    private store: IncidentStore,
    private workflowStore: any,
    private scheduleStore: any
  ) {}

  async pollForStuckWorkflows(tenant_id: string) {
    // A workflow is "stuck" if it's been in 'running' state for more than 5 minutes without update
    const threshold = Date.now() - 5 * 60 * 1000;
    const stuck = await this.workflowStore.list_stuck_workflow_instances({ tenant_id, threshold });

    for (const inst of stuck) {
      await this.store.create_incident({
        tenant_id,
        source_type: "workflow",
        source_id: inst.id,
        incident_type: "workflow_stuck",
        message: `Workflow ${inst.id} (spec: ${inst.spec_id}) is stuck in running state.`,
        status: "open",
        context_json: JSON.stringify(inst),
        created_ts: Date.now(),
      });
      // Mark as failed so it doesn't keep getting picked up as stuck, 
      // or we could have a 'stalled' status. For now, let's keep it 'running' but create incident once.
      // In a real system we'd use an idempotency key or check if incident already exists.
    }
  }

  async pollForFailedSchedules(tenant_id: string) {
    const failed = await this.scheduleStore.list_failed_schedules({ tenant_id });

    for (const sched of failed) {
      await this.store.create_incident({
        tenant_id,
        source_type: "schedule",
        source_id: sched.id,
        incident_type: "schedule_failed",
        message: `Schedule ${sched.id} failed to execute.`,
        status: "open",
        context_json: JSON.stringify(sched),
        created_ts: Date.now(),
      });
    }
  }

  async retryWorkflow(tenant_id: string, workflow_id: string) {
    const inst = await this.workflowStore.get_workflow_instance(tenant_id, workflow_id);
    if (!inst) throw new Error("Workflow instance not found");

    // Reset to running/failed state for worker to pick up? 
    // Actually, let's just update the updated_ts so it's not "stuck" anymore and maybe the worker picks it up
    // Or if it was truly failed, we change status.
    await this.workflowStore.update_workflow_instance(tenant_id, workflow_id, {
      status: "running",
      updated_ts: Date.now()
    });
  }

  async retrySchedule(tenant_id: string, schedule_id: string) {
    // Reset status to pending and set next_run to now
    await this.scheduleStore.update_schedule(tenant_id, schedule_id, {
      status: "pending",
      next_run_ts: Date.now()
    });
  }
}
