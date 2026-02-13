import type { CoreIrBundleV0 } from "../../core/ir/types"
import { bundleHash } from "../db/bundle-registry"
import { getBundle } from "../db/bundle-registry"
import { getTenantBinding } from "../db/tenant-binding"

type D1Database = {
  exec: (sql: string) => Promise<any>
  prepare: (sql: string) => {
    bind: (...args: any[]) => {
      run: () => Promise<any>
      first: <T = any>() => Promise<T | null>
    }
  }
}

export async function loadTenantBundle (db: D1Database, tenant_id: string): Promise<{
  bundle: CoreIrBundleV0
  bundle_hash: string
  active_version: number
}> {
  const binding = await getTenantBinding(db, tenant_id)
  if (!binding) throw new Error(`tenant not bound: ${tenant_id}`)

  const bundle = await getBundle(db, binding.bundle_hash)
  if (!bundle) throw new Error(`bundle not found: ${binding.bundle_hash}`)
  const computedHash = bundleHash(bundle)
  if (computedHash !== binding.bundle_hash) {
    throw new Error(`bundle hash verification failed: expected ${binding.bundle_hash} got ${computedHash}`)
  }

  return {
    bundle,
    bundle_hash: binding.bundle_hash,
    active_version: binding.active_version,
  }
}
