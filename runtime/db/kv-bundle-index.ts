export interface KVNamespace {
  put(key: string, value: string): Promise<void>;
  get(key: string): Promise<string | null>;
  list(options?: { prefix?: string }): Promise<{ keys: { name: string }[] }>;
}

export class KVBundleIndex {
  constructor(private kv: KVNamespace) {}

  async registerBundle(name: string, version: string, digest: string): Promise<void> {
    // Index latest version
    const latestKey = `bundles:latest:${name}`;
    const currentLatest = await this.kv.get(latestKey);
    
    // Simplistic semver comparison (real impl would use semver lib)
    if (!currentLatest || version >= (JSON.parse(currentLatest).version)) {
      await this.kv.put(latestKey, JSON.stringify({ version, digest }));
    }

    // Index specific version
    const versionKey = `bundles:version:${name}:${version}`;
    await this.kv.put(versionKey, digest);
  }

  async getDigest(name: string, version: string = "latest"): Promise<string | null> {
    if (version === "latest") {
      const data = await this.kv.get(`bundles:latest:${name}`);
      return data ? JSON.parse(data).digest : null;
    }
    return await this.kv.get(`bundles:version:${name}:${version}`);
  }
}
