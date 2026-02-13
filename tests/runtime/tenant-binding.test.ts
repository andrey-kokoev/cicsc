import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { bindTenant, getTenantBinding, listTenantBindingAudit } from "../../runtime/db/tenant-binding"

function makeFakeDb () {
  const map = new Map<string, { bundle_hash: string; active_version: number }>()
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
                if (sql.includes("INSERT INTO tenant_bindings")) {
                  const [tenant_id, bundle_hash, active_version] = args
                  map.set(String(tenant_id), {
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
              async all<T = any> () {
                if (sql.includes("FROM tenant_binding_audit")) {
                  const [tenant_id] = args
                  const rows = audit.filter((r) => r.tenant_id === String(tenant_id))
                  return { results: rows as T[] }
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

  it("records immutable audit trail entries for each bind change", async () => {
    const fake = makeFakeDb()
    await bindTenant(fake.db as any, { tenant_id: "t1", bundle_hash: "h1", active_version: 0 })
    await bindTenant(fake.db as any, { tenant_id: "t1", bundle_hash: "h2", active_version: 1 })
    await bindTenant(fake.db as any, { tenant_id: "t1", bundle_hash: "h2", active_version: 2 })

    const rows = await listTenantBindingAudit(fake.db as any, "t1")
    assert.equal(rows.length, 3)
    assert.deepEqual(rows.map((r) => r.audit_id), [1, 2, 3])
    assert.deepEqual(rows.map((r) => r.prev_bundle_hash), [null, "h1", "h2"])
    assert.deepEqual(rows.map((r) => r.next_bundle_hash), ["h1", "h2", "h2"])
    assert.deepEqual(rows.map((r) => r.next_active_version), [0, 1, 2])
  })
})
