import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { bindTenant, getTenantBinding } from "../../runtime/db/tenant-binding"

function makeFakeDb () {
  const map = new Map<string, { bundle_hash: string; active_version: number }>()

  return {
    db: {
      async exec (_sql: string) {
        return { ok: true }
      },
      prepare (sql: string) {
        return {
          bind (...args: any[]) {
            return {
              async run () {
                if (sql.includes("INSERT INTO tenant_bindings")) {
                  const [tenant_id, bundle_hash, active_version] = args
                  map.set(String(tenant_id), {
                    bundle_hash: String(bundle_hash),
                    active_version: Number(active_version),
                  })
                }
                return { success: true }
              },
              async first<T = any> () {
                if (sql.includes("SELECT tenant_id, bundle_hash, active_version")) {
                  const [tenant_id] = args
                  const row = map.get(String(tenant_id))
                  if (!row) return null
                  return {
                    tenant_id: String(tenant_id),
                    bundle_hash: row.bundle_hash,
                    active_version: row.active_version,
                  } as T
                }
                return null
              },
            }
          },
        }
      },
    },
  }
}

describe("tenant binding", () => {
  it("binds and retrieves tenant -> bundle/version mapping", async () => {
    const fake = makeFakeDb()
    await bindTenant(fake.db as any, { tenant_id: "t1", bundle_hash: "h1", active_version: 0 })
    const row = await getTenantBinding(fake.db as any, "t1")
    assert.deepEqual(row, { tenant_id: "t1", bundle_hash: "h1", active_version: 0 })
  })

  it("updates existing binding on rebind", async () => {
    const fake = makeFakeDb()
    await bindTenant(fake.db as any, { tenant_id: "t1", bundle_hash: "h1", active_version: 0 })
    await bindTenant(fake.db as any, { tenant_id: "t1", bundle_hash: "h2", active_version: 2 })
    const row = await getTenantBinding(fake.db as any, "t1")
    assert.deepEqual(row, { tenant_id: "t1", bundle_hash: "h2", active_version: 2 })
  })
})
