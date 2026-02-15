// runtime/db/schedule-store.ts

export type ScheduledJobStatus = "pending" | "executing" | "completed" | "failed" | "canceled"

export type ScheduledJob = {
  id: string
  schedule_name: string

  trigger_type: "cron" | "delay" | "event"
  entity_type?: string
  entity_id?: string
  event_type?: string

  scheduled_at: number // Unix ms
  timezone?: string

  command_entity: string
  command_name: string
  input_json: string

  queue_name?: string

  status: ScheduledJobStatus
  attempts: number
  last_error?: string
  next_retry_at?: number

  created_at: number
  updated_at: number
  executed_at?: number
}

export interface ScheduleStore {
  /**
   * Schedule a new job.
   */
  scheduleJob (tenant_id: string, job: Omit<ScheduledJob, "id" | "status" | "attempts" | "created_at" | "updated_at">): Promise<string>

  /**
   * List jobs due for execution.
   */
  listDueJobs (tenant_id: string, now: number, limit?: number): Promise<ScheduledJob[]>

  /**
   * Mark a job as executing (lock it).
   */
  markExecuting (tenant_id: string, jobId: string, now: number): Promise<boolean>

  /**
   * Complete a job successfully.
   */
  completeJob (tenant_id: string, jobId: string, now: number): Promise<void>

  /**
   * Mark a job as failed, potentially setting up a retry.
   */
  failJob (tenant_id: string, jobId: string, error: string, nextRetryAt?: number): Promise<void>

  /**
   * Delete or cancel a job.
   */
  cancelJob (tenant_id: string, jobId: string): Promise<void>

  /**
   * Get a job by ID.
   */
  getJob (tenant_id: string, jobId: string): Promise<ScheduledJob | null>

  /**
   * List jobs for a specific entity (e.g. all follow-ups for a ticket).
   */
  listJobsForEntity (tenant_id: string, entityType: string, entityId: string): Promise<ScheduledJob[]>
  /**
   * Get metrics for schedules.
   */
  getScheduleMetrics (tenant_id: string): Promise<{ pending_count: number; failed_count: number; avg_latency_ms: number }>

  /**
   * CRON management
   */
  upsertCronSchedule (params: { tenant_id: string, name: string, expression: string, timezone?: string, next_run_at: number }): Promise<void>
  listDueCronSchedules (params: { tenant_id: string, now: number }): Promise<any[]>
  updateCronLastRun (params: { tenant_id: string, name: string, last_run_at: number, next_run_at: number }): Promise<void>
}
