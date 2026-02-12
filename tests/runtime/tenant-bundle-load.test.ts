import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { putBundle } from "../../runtime/db/bundle-registry"
import { bindTenant } from "../../runtime/db/tenant-binding"
import { loadTenantBundle } from "../../runtime/http/tenant-bundle"

function makeFakeDb () {
  const bundles = new Map<string, string>()
  const bindings = new Map<string, { bundle_hash: string; active_version: number }>()

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
                if (sql.includes("INSERT INTO bundle_registry")) {
                  const [hash, json] = args
                  if (!bundles.has(String(hash))) bundles.set(String(hash), String(json))
                } else if (sql.includes("INSERT INTO tenant_bindings")) {
                  const [tenant_id, bundle_hash, active_version] = args
                  bindings.set(String(tenant_id), {
                    bundle_hash: String(bundle_hash),
                    active_version: Number(active_version),
                  })
                }
                return { success: true }
              },
              async first<T = any> () {
                if (sql.includes("SELECT bundle_json FROM bundle_registry")) {
                  const [hash] = args
                  const json = bundles.get(String(hash))
                  if (!json) return null
                  return { bundle_json: json } as T
                }
                if (sql.includes("SELECT tenant_id, bundle_hash, active_version")) {
                  const [tenant_id] = args
                  const b = bindings.get(String(tenant_id))
                  if (!b) return null
                  return {
                    tenant_id: String(tenant_id),
                    bundle_hash: b.bundle_hash,
                    active_version: b.active_version,
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

describe("tenant bundle loading", () => {
  it("loads bundle by tenant binding", async () => {
    const fake = makeFakeDb()
    const bundle: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            commands: { c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] } },
            reducer: {},
          },
        },
      },
    }

    const put = await putBundle(fake.db as any, bundle)
    await bindTenant(fake.db as any, { tenant_id: "t1", bundle_hash: put.bundle_hash, active_version: 0 })

    const loaded = await loadTenantBundle(fake.db as any, "t1")
    assert.equal(loaded.bundle_hash, put.bundle_hash)
    assert.equal(loaded.active_version, 0)
    assert.deepEqual(loaded.bundle, bundle)
  })

  it("fails when tenant has no binding", async () => {
    const fake = makeFakeDb()
    await assert.rejects(async () => {
      await loadTenantBundle(fake.db as any, "missing")
    }, /tenant not bound/)
  })
})
