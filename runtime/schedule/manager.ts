// runtime/schedule/manager.ts

import type { CoreIrV0 } from "../../core/ir/types"
import type { ScheduleStore } from "../db/schedule-store"
import { evalExpr, type VmEnv, type VmIntrinsics } from "../../core/vm/eval"

export class ScheduleManager {
  constructor(
    private store: ScheduleStore,
    private ir: CoreIrV0,
    private intrinsics: VmIntrinsics
  ) { }

  /**
   * Hook to be called after events are appended.
   */
  async onEventsEmitted (params: {
    tenant_id: string
    entity_type: string
    entity_id: string
    events: { event_type: string; payload: any; ts: number; actor_id: string }[]
    env?: Partial<VmEnv> // Optional context from the command execution
  }) {
    const { tenant_id, entity_type, entity_id, events, env: baseEnv } = params

    for (const [sName, spec] of Object.entries(this.ir.schedules ?? {})) {
      if (!spec.trigger || !("on_event" in spec.trigger)) continue

      const trigger = spec.trigger as { on_event: string; delay_seconds?: number }

      for (const event of events) {
        if (event.event_type !== trigger.on_event) continue

        const env: VmEnv = {
          now: event.ts,
          actor: event.actor_id,
          state: baseEnv?.state ?? "",
          input: baseEnv?.input ?? {},
          attrs: baseEnv?.attrs ?? {},
          row: {},
          arg: {},
          intrinsics: this.intrinsics,
          policies: baseEnv?.policies,
          e: { type: event.event_type, actor: event.actor_id, time: event.ts, payload: event.payload }
        }

        // Check condition if any
        if (spec.condition) {
          const ok = evalExpr(spec.condition, env)
          if (!ok) continue
        }

        // Schedule it
        const scheduledAt = event.ts + (trigger.delay_seconds ?? 0) * 1000

        // Compute input_map
        const inputMap: Record<string, any> = {}
        for (const [k, ex] of Object.entries(spec.action.input_map)) {
          inputMap[k] = evalExpr(ex, env)
        }

        await this.store.scheduleJob(tenant_id, {
          schedule_name: sName,
          trigger_type: "event",
          entity_type,
          entity_id,
          event_type: event.event_type,
          scheduled_at: scheduledAt,
          command_entity: spec.action.entity_type,
          command_name: spec.action.command,
          input_json: JSON.stringify(inputMap),
          queue_name: spec.queue,
          timezone: spec.execution?.timezone
        })
      }
    }
  }
}
