export type ProjectionCacheKey = {
  tenant_id: string
  view_name: string
  args_hash: string
}

export type ProjectionCacheEntry = {
  rows: any[]
  computed_at: number
  source_seq_hint?: number
}

export class ProjectionCache {
  private readonly map = new Map<string, ProjectionCacheEntry>()

  constructor (private readonly maxEntries = 512) {}

  get (key: ProjectionCacheKey): ProjectionCacheEntry | null {
    const k = encodeKey(key)
    const v = this.map.get(k)
    if (!v) return null

    // LRU touch
    this.map.delete(k)
    this.map.set(k, v)
    return v
  }

  set (key: ProjectionCacheKey, entry: ProjectionCacheEntry): void {
    const k = encodeKey(key)
    if (this.map.has(k)) this.map.delete(k)
    this.map.set(k, entry)
    this.evictIfNeeded()
  }

  invalidateTenant (tenant_id: string): void {
    for (const k of this.map.keys()) {
      if (!k.startsWith(`${tenant_id}|`)) continue
      this.map.delete(k)
    }
  }

  size (): number {
    return this.map.size
  }

  private evictIfNeeded () {
    while (this.map.size > this.maxEntries) {
      const oldest = this.map.keys().next().value
      if (!oldest) return
      this.map.delete(oldest)
    }
  }
}

function encodeKey (k: ProjectionCacheKey): string {
  return `${k.tenant_id}|${k.view_name}|${k.args_hash}`
}
