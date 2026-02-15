// /runtime/queue/worker.ts

import { type CoreIrV0, type ExprV0 } from "../../core/ir/types"
import { evalExpr, type VmIntrinsics, type Value, type VmEnv } from "../../core/vm/eval"
import { executeCommand } from "../execute-command"
import type { D1Store } from "../db/d1-store"

export class QueueWorker {
  constructor(
    private ir: CoreIrV0,
    private store: D1Store,
    private intrinsics: VmIntrinsics
  ) { }

  /**
   * Process a batch of messages from a specific queue.
   */
  async processQueue (tenant_id: string, queueName: string, batchSize: number = 10) {
    const queueSpec = this.ir.queues?.[queueName]
    if (!queueSpec) return
    if (!queueSpec.map_to) return

    for (let i = 0; i < batchSize; i++) {
      // 1. Dequeue (with 30s visibility timeout)
      const msg = await this.store.dequeue({
        tenant_id,
        queue_name: queueName,
        visibility_timeout_ms: 30000
      })
      if (!msg) break

      try {
        // 2. Transform Message -> Command Input
        const input = this.transformMessage(msg.payload, queueSpec.map_to.input_map)

        // 3. Determine Entity ID
        // If not explicitly mapped, try to find it in the payload.
        const entity_id = String(input.entity_id ?? (msg.payload as any).entity_id ?? "unknown")

        // 4. Execute Command (Idempotent by msg.id)
        const command_id = msg.idempotency_key || `queue:${queueName}:${msg.id}`

        await executeCommand({
          ir: this.ir,
          store: this.store,
          intrinsics: this.intrinsics,
          req: {
            tenant_id,
            actor_id: "system:queue:" + queueName,
            command_id,
            entity_type: queueSpec.map_to.entity_type,
            entity_id,
            command_name: queueSpec.map_to.command,
            input,
            now: Date.now()
          }
        })

        // 5. Success -> Ack (Delete from queue)
        await this.store.ack({ tenant_id, queue_name: queueName, message_id: msg.id })

        // Optional: record worker-side idempotency in idempotency_keys
        // (Implementation omitted for v0/BN2.3)

      } catch (error) {
        // 6. Failure -> Retry or Dead Letter
        if (msg.attempts >= queueSpec.delivery.max_attempts) {
          await this.store.deadLetter({
            tenant_id,
            queue_name: queueName,
            message_id: msg.id,
            error: String(error)
          })
        } else {
          const delay = this.calculateBackoff(msg.attempts, queueSpec.delivery)
          await this.store.retry({
            tenant_id,
            queue_name: queueName,
            message_id: msg.id,
            delay_ms: delay
          })
        }
      }
    }
  }

  private transformMessage (payload: any, inputMap: Record<string, ExprV0>): Record<string, Value> {
    const env: VmEnv = {
      now: Date.now(),
      actor: "system:queue",
      state: "none",
      input: {},
      attrs: {},
      payload,    // available via var.payload per IR extension
      row: {},
      arg: {},
      intrinsics: this.intrinsics,
    }

    const out: Record<string, Value> = {}
    for (const [k, expr] of Object.entries(inputMap)) {
      out[k] = evalExpr(expr, env)
    }
    return out
  }

  private calculateBackoff (attempts: number, delivery: any): number {
    const delay = delivery.initial_backoff_ms * Math.pow(2, Math.max(0, attempts - 1))
    return Math.min(delay, delivery.max_backoff_ms)
  }
}
