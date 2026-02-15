import { S3Adapter, S3Config } from "./s3"

export interface R2Config extends S3Config {
  accountId: string
  // R2 uses S3-compatible API but with Cloudflare-specific endpoint format
}

export class R2Adapter extends S3Adapter {
  readonly id = "r2"
  
  constructor(config: R2Config) {
    // R2 endpoint format: https://<accountId>.r2.cloudflarestorage.com
    const r2Endpoint = config.endpoint || 
      `https://${config.accountId}.r2.cloudflarestorage.com`
    
    super({
      ...config,
      endpoint: r2Endpoint,
      region: "auto" // R2 doesn't use regions like S3
    })
  }
  
  validateConfig(): boolean {
    const baseValid = super.validateConfig()
    return baseValid && !!(this.config as R2Config).accountId
  }
}
