import type { Event } from "../../core/runtime/replay"

export class KernelMemoryBackend {
  private readonly events: Event[] = []

  append (batch: Event[]): void {
    for (const e of batch) this.events.push({ ...e, payload: { ...(e.payload as any) } })
  }

  readAll (): Event[] {
    return this.events
      .map((e) => ({ ...e, payload: { ...(e.payload as any) } }))
      .sort((a, b) =>
        cmp(a.tenant_id, b.tenant_id) ||
        cmp(a.entity_type, b.entity_type) ||
        cmp(a.entity_id, b.entity_id) ||
        a.seq - b.seq ||
        a.ts - b.ts
      )
  }

  clear (): void {
    this.events.length = 0
  }
}

function cmp (a: string, b: string): number {
  return a < b ? -1 : a > b ? 1 : 0
}
