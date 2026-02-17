export class EntityStore {
  private apiUrl: string
  private cache: Map<string, { data: any; timestamp: number }> = new Map()
  private cacheTimeout = 5000

  constructor(apiUrl: string) {
    this.apiUrl = apiUrl
  }

  async list(entity: string, options?: { query?: Record<string, any> }): Promise<any[]> {
    const cacheKey = `list:${entity}:${JSON.stringify(options?.query || {})}`
    const cached = this.getFromCache(cacheKey)
    if (cached) return cached

    const url = new URL(`${this.apiUrl}/api/${entity}`)
    if (options?.query) {
      Object.entries(options.query).forEach(([k, v]) => url.searchParams.set(k, String(v)))
    }

    const response = await fetch(url.toString())
    if (!response.ok) throw new Error(`Failed to list ${entity}: ${response.statusText}`)

    const data = await response.json()
    this.setToCache(cacheKey, data)
    return data
  }

  async get(entity: string, id: string): Promise<any> {
    const cacheKey = `get:${entity}:${id}`
    const cached = this.getFromCache(cacheKey)
    if (cached) return cached

    const response = await fetch(`${this.apiUrl}/api/${entity}/${id}`)
    if (!response.ok) throw new Error(`Failed to get ${entity}/${id}: ${response.statusText}`)

    const data = await response.json()
    this.setToCache(cacheKey, data)
    return data
  }

  async create(entity: string, data: any): Promise<any> {
    const response = await fetch(`${this.apiUrl}/api/${entity}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(data),
    })

    if (!response.ok) throw new Error(`Failed to create ${entity}: ${response.statusText}`)

    this.invalidateCache(entity)
    return response.json()
  }

  async update(entity: string, id: string, data: any): Promise<any> {
    const response = await fetch(`${this.apiUrl}/api/${entity}/${id}`, {
      method: "PATCH",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(data),
    })

    if (!response.ok) throw new Error(`Failed to update ${entity}/${id}: ${response.statusText}`)

    this.invalidateCache(entity)
    return response.json()
  }

  async delete(entity: string, id: string): Promise<void> {
    const response = await fetch(`${this.apiUrl}/api/${entity}/${id}`, {
      method: "DELETE",
    })

    if (!response.ok) throw new Error(`Failed to delete ${entity}/${id}: ${response.statusText}`)

    this.invalidateCache(entity)
  }

  async execute(entity: string, command: string, id: string, input?: any): Promise<any> {
    const response = await fetch(`${this.apiUrl}/api/${entity}/${id}/${command}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(input || {}),
    })

    if (!response.ok) throw new Error(`Failed to execute ${command} on ${entity}/${id}: ${response.statusText}`)

    this.invalidateCache(entity)
    return response.json()
  }

  private getFromCache(key: string): any | null {
    const entry = this.cache.get(key)
    if (!entry) return null

    if (Date.now() - entry.timestamp > this.cacheTimeout) {
      this.cache.delete(key)
      return null
    }

    return entry.data
  }

  private setToCache(key: string, data: any): void {
    this.cache.set(key, { data, timestamp: Date.now() })
  }

  private invalidateCache(entity: string): void {
    const keysToDelete: string[] = []
    this.cache.forEach((_, key) => {
      if (key.includes(`:${entity}:`)) {
        keysToDelete.push(key)
      }
    })
    keysToDelete.forEach((key) => this.cache.delete(key))
  }

  clearCache(): void {
    this.cache.clear()
  }
}

export function createStore(apiUrl: string): EntityStore {
  return new EntityStore(apiUrl)
}
