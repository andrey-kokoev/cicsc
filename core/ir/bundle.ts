import type { CoreIrV0 } from "./types"

/**
 * A Bundle is a self-contained unit of distribution for a CICSC system.
 * It contains the compiled IR, metadata, and versioning info.
 */
export type BundleV1 = {
  kind: "cicsc/bundle"
  version: 1
  manifest: BundleManifestV1
  core_ir: CoreIrV0
  digest?: string // SHA-256 of manifest + core_ir
}

export type BundleManifestV1 = {
  name: string
  version: string // SemVer
  author?: string
  description?: string
  dependencies?: Record<string, string> // name -> version range
  published_at?: string // ISO-8601
  deprecated?: {
    since: string
    message: string
    eol_at?: string
  }
}
