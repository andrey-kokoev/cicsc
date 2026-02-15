// /runtime/db/queue-store.ts

export type QueueMessage = {
  id: string
  payload: any
  attempts: number
  visible_after: number
  created_at: number
  idempotency_key?: string
}

export interface QueueStore {
  enqueue (params: {
    tenant_id: string
    queue_name: string
    message: any
    idempotency_key?: string
  }): Promise<void>

  dequeue (params: {
    tenant_id: string
    queue_name: string
    visibility_timeout_ms: number
  }): Promise<QueueMessage | null>

  ack (params: {
    tenant_id: string
    queue_name: string
    message_id: string
  }): Promise<void>

  retry (params: {
    tenant_id: string
    queue_name: string
    message_id: string
    delay_ms: number
  }): Promise<void>

  deadLetter (params: {
    tenant_id: string
    queue_name: string
    message_id: string
    error: string
  }): Promise<void>

  getMetrics (params: {
    tenant_id: string
    queue_name: string
  }): Promise<{
    depth: number
    oldest_message_age_seconds: number | null
    dlq_size: number
  }>

  listDlq (params: {
    tenant_id: string
    queue_name: string
    limit?: number
  }): Promise<any[]>

  replayDlq (params: {
    tenant_id: string
    queue_name: string
    message_id: string
  }): Promise<void>
}
