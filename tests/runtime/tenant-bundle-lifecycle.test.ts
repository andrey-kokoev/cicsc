import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { publishBundle, resolveBundle } from "../../runtime/db/bundle-contract"
import { bindTenant, getTenantBinding, listTenantBindingAudit } from "../../runtime/db/tenant-binding"
import { loadTenantBundle } from "../../runtime/http/tenant-bundle"

function makeFakeDb () {
  const bundles = new Map<string, string>()
  const bindings = new Map<string, { bundle_hash: string; active_version: number }>()
  const audit: Array<{
    audit_id: number
    tenant_id: string
    prev_bundle_hash: string | null
    prev_active_version: number | null
    next_bundle_hash: string
    next_active_version: number
    changed_ts: number
  }> = []
  let nextAuditId = 1

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
                  const [bundle_hash, bundle_json] = args
                  if (!bundles.has(String(bundle_hash))) bundles.set(String(bundle_hash), String(bundle_json))
                } else if (sql.includes("INSERT INTO tenant_bindings")) {
                  const [tenant_id, bundle_hash, active_version] = args
                  bindings.set(String(tenant_id), {
                    bundle_hash: String(bundle_hash),
                    active_version: Number(active_version),
                  })
                } else if (sql.includes("INSERT INTO tenant_binding_audit")) {
                  const [tenant_id, prev_bundle_hash, prev_active_version, next_bundle_hash, next_active_version, changed_ts] = args
                  audit.push({
                    audit_id: nextAuditId++,
                    tenant_id: String(tenant_id),
                    prev_bundle_hash: prev_bundle_hash == null ? null : String(prev_bundle_hash),
                    prev_active_version: prev_active_version == null ? null : Number(prev_active_version),
                    next_bundle_hash: String(next_bundle_hash),
                    next_active_version: Number(next_active_version),
                    changed_ts: Number(changed_ts),
                  })
                }
                return { success: true }
              },
              async first<T = any> () {
                if (sql.includes("SELECT bundle_json FROM bundle_registry")) {
                  const [bundle_hash] = args
                  const bundle_json = bundles.get(String(bundle_hash))
                  if (!bundle_json) return null
                  return { bundle_json } as T
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
              async all<T = any> () {
                if (sql.includes("FROM tenant_binding_audit")) {
                  const [tenant_id] = args
                  return { results: audit.filter((a) => a.tenant_id === String(tenant_id)) as T[] }
                }
                return { results: [] as T[] }
              },
            }
          },
        }
      },
    },
  }
}

describe("tenant bundle lifecycle", () => {
  it("supports publish/bind/upgrade/rollback with deterministic audit trail", async () => {
    const fake = makeFakeDb()
    const bundleV0: any = {
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
    const bundleV1: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["open"],
            initial_state: "open",
            attrs: {},
            commands: { c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] } },
            reducer: {},
          },
        },
      },
    }

    const pub0 = await publishBundle(fake.db as any, bundleV0)
    const pub1 = await publishBundle(fake.db as any, bundleV1)
    assert.ok(await resolveBundle(fake.db as any, pub0.bundle_hash))
    assert.ok(await resolveBundle(fake.db as any, pub1.bundle_hash))

    await bindTenant(fake.db as any, { tenant_id: "tenant-a", bundle_hash: pub0.bundle_hash, active_version: 0 })
    let current = await getTenantBinding(fake.db as any, "tenant-a")
    assert.equal(current?.bundle_hash, pub0.bundle_hash)
    assert.equal((await loadTenantBundle(fake.db as any, "tenant-a")).bundle_hash, pub0.bundle_hash)

    await bindTenant(fake.db as any, { tenant_id: "tenant-a", bundle_hash: pub1.bundle_hash, active_version: 1 })
    current = await getTenantBinding(fake.db as any, "tenant-a")
    assert.equal(current?.bundle_hash, pub1.bundle_hash)
    assert.equal(current?.active_version, 1)
    assert.equal((await loadTenantBundle(fake.db as any, "tenant-a")).bundle_hash, pub1.bundle_hash)

    await bindTenant(fake.db as any, { tenant_id: "tenant-a", bundle_hash: pub0.bundle_hash, active_version: 0 })
    current = await getTenantBinding(fake.db as any, "tenant-a")
    assert.equal(current?.bundle_hash, pub0.bundle_hash)
    assert.equal(current?.active_version, 0)
    assert.equal((await loadTenantBundle(fake.db as any, "tenant-a")).bundle_hash, pub0.bundle_hash)

    const audit = await listTenantBindingAudit(fake.db as any, "tenant-a")
    assert.equal(audit.length, 3)
    assert.deepEqual(audit.map((r) => r.next_bundle_hash), [pub0.bundle_hash, pub1.bundle_hash, pub0.bundle_hash])
    assert.deepEqual(audit.map((r) => r.next_active_version), [0, 1, 0])
  })
})
