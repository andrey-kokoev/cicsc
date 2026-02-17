export interface Secret {
  key: string
  value: string
  encrypted: boolean
  created_at: string
  updated_at: string
}

export interface SecretsManager {
  get(tenantId: string, key: string): Promise<Secret | null>
  set(tenantId: string, key: string, value: string): Promise<void>
  delete(tenantId: string, key: string): Promise<void>
  list(tenantId: string): Promise<Secret[]>
  rotate(tenantId: string, key: string, newValue: string): Promise<void>
}

export class EnvSecretsManager implements SecretsManager {
  private prefix = "CISC_"

  async get(tenantId: string, key: string): Promise<Secret | null> {
    const envKey = this.getEnvKey(tenantId, key)
    const value = process.env[envKey]
    
    if (!value) return null

    return {
      key,
      value,
      encrypted: false,
      created_at: new Date().toISOString(),
      updated_at: new Date().toISOString(),
    }
  }

  async set(tenantId: string, key: string, value: string): Promise<void> {
    const envKey = this.getEnvKey(tenantId, key)
    process.env[envKey] = value
  }

  async delete(tenantId: string, key: string): Promise<void> {
    const envKey = this.getEnvKey(tenantId, key)
    delete process.env[envKey]
  }

  async list(tenantId: string): Promise<Secret[]> {
    const secrets: Secret[] = []
    const prefix = this.prefix + tenantId.toUpperCase() + "_"
    
    for (const [envKey, value] of Object.entries(process.env)) {
      if (envKey.startsWith(prefix)) {
        const key = envKey.slice(prefix.length)
        secrets.push({
          key,
          value: value || "",
          encrypted: false,
          created_at: new Date().toISOString(),
          updated_at: new Date().toISOString(),
        })
      }
    }
    
    return secrets
  }

  async rotate(tenantId: string, key: string, newValue: string): Promise<void> {
    await this.set(tenantId, key, newValue)
  }

  private getEnvKey(tenantId: string, key: string): string {
    return this.prefix + tenantId.toUpperCase() + "_" + key.toUpperCase()
  }
}

export class ApiKeyManager {
  private apiKeys: Map<string, { key: string; tenantId: string; createdAt: Date }> = new Map()

  async create(tenantId: string): Promise<string> {
    const key = this.generateKey()
    this.apiKeys.set(key, { key, tenantId, createdAt: new Date() })
    return key
  }

  async validate(key: string): Promise<{ valid: boolean; tenantId?: string }> {
    const entry = this.apiKeys.get(key)
    if (!entry) return { valid: false }
    return { valid: true, tenantId: entry.tenantId }
  }

  async revoke(key: string): Promise<void> {
    this.apiKeys.delete(key)
  }

  async list(tenantId: string): Promise<string[]> {
    const keys: string[] = []
    for (const [, entry] of this.apiKeys) {
      if (entry.tenantId === tenantId) {
        keys.push(entry.key)
      }
    }
    return keys
  }

  private generateKey(): string {
    const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
    let result = "cicsc_"
    for (let i = 0; i < 32; i++) {
      result += chars.charAt(Math.floor(Math.random() * chars.length))
    }
    return result
  }
}

export function createSecretsManager(): SecretsManager {
  return new EnvSecretsManager()
}

export function createApiKeyManager(): ApiKeyManager {
  return new ApiKeyManager()
}
