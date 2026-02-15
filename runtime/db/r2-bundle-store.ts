import type { BundleV1 } from "../../core/ir/bundle"

/**
 * Interface for Cloudflare R2 Bucket or S3-compatible store.
 */
export interface R2Bucket {
  put (key: string, value: string | ArrayBuffer): Promise<void>
  get (key: string): Promise<R2Object | null>
}

export interface R2Object {
  text (): Promise<string>
}

export class R2BundleStore {
  constructor(private bucket: R2Bucket) { }

  async upload (bundle: BundleV1): Promise<void> {
    if (!bundle.digest) {
      throw new Error("Cannot upload unsealed bundle (no digest)")
    }
    const key = `bundles/${bundle.manifest.name}/${bundle.manifest.version}/${bundle.digest}.json`
    await this.bucket.put(key, JSON.stringify(bundle))
  }

  async download (name: string, version: string, digest: string): Promise<BundleV1 | null> {
    const key = `bundles/${name}/${version}/${digest}.json`
    const obj = await this.bucket.get(key)
    if (!obj) return null
    return JSON.parse(await obj.text()) as BundleV1
  }

  /**
   * Helper to construct a legacy D1 registry entry from an R2-stored bundle
   */
  async syncToRegistry (db: any, name: string, version: string, digest: string): Promise<void> {
    const bundle = await this.download(name, version, digest)
    if (!bundle) throw new Error("Bundle not found in R2")
    // Implementation would call putBundle in the registry
  }
}
