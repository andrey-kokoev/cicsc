export interface KVNamespace {
  put (key: string, value: string): Promise<void>
  get (key: string): Promise<string | null>
  list (options?: { prefix?: string }): Promise<{ keys: { name: string }[] }>
}

export class KVBundleIndex {
  constructor(private kv: KVNamespace) { }

  async registerBundle (name: string, version: string, digest: string): Promise<void> {
    // Index latest version
    const latestKey = `bundles:latest:${name}`
    const currentLatest = await this.kv.get(latestKey)

    // Simplistic semver comparison (real impl would use semver lib)
    if (!currentLatest || version >= (JSON.parse(currentLatest).version)) {
      await this.kv.put(latestKey, JSON.stringify({ version, digest }))
    }

    // Index specific version
    const versionKey = `bundles:version:${name}:${version}`
    await this.kv.put(versionKey, digest)

    // Maintain a list of versions
    const listKey = `bundles:list:${name}`
    const listJson = await this.kv.get(listKey)
    const list = listJson ? JSON.parse(listJson) : []
    if (!list.includes(version)) {
      list.push(version)
      await this.kv.put(listKey, JSON.stringify(list))
    }
  }

  async listVersions (name: string): Promise<string[]> {
    const listJson = await this.kv.get(`bundles:list:${name}`)
    return listJson ? JSON.parse(listJson) : []
  }

  async deprecate (name: string, version: string, message: string): Promise<void> {
    const key = `bundles:deprecation:${name}:${version}`
    await this.kv.put(key, JSON.stringify({ message, at: new Date().toISOString() }))
  }

  async checkDeprecation (name: string, version: string): Promise<{ message: string, at: string } | null> {
    const data = await this.kv.get(`bundles:deprecation:${name}:${version}`)
    return data ? JSON.parse(data) : null
  }

  async getDigest (name: string, version: string = "latest"): Promise<string | null> {
    if (version === "latest") {
      const data = await this.kv.get(`bundles:latest:${name}`)
      return data ? JSON.parse(data).digest : null
    }
    return await this.kv.get(`bundles:version:${name}:${version}`)
  }
}
