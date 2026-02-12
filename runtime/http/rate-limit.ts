export type RateLimitDecision = {
  ok: boolean
  retry_after_seconds?: number
}

export class TenantTokenBucketLimiter {
  private readonly buckets = new Map<string, { tokens: number; last_ms: number }>()

  constructor (
    private readonly capacity: number,
    private readonly refill_per_second: number
  ) {}

  check (tenant_id: string, now_ms: number): RateLimitDecision {
    const prev = this.buckets.get(tenant_id) ?? { tokens: this.capacity, last_ms: now_ms }
    const elapsed = Math.max(0, (now_ms - prev.last_ms) / 1000)
    const refilled = Math.min(this.capacity, prev.tokens + elapsed * this.refill_per_second)

    if (refilled >= 1) {
      this.buckets.set(tenant_id, { tokens: refilled - 1, last_ms: now_ms })
      return { ok: true }
    }

    const deficit = 1 - refilled
    const retry = Math.ceil(deficit / this.refill_per_second)
    this.buckets.set(tenant_id, { tokens: refilled, last_ms: now_ms })
    return { ok: false, retry_after_seconds: Math.max(1, retry) }
  }
}
