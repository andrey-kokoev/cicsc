import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

import { publishBundle, resolveBundle } from "../../runtime/db/bundle-contract"
import { bindTenant, getTenantBinding, listTenantBindingAudit } from "../../runtime/db/tenant-binding"

function makeFakeDb () {
  const bundles = new Map<string, string>()
  const bindings = new Map<string, { bundle_hash: string; active_version: number }>()
  const audit: Array<any> = []
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

describe("phase6 sdk contract", () => {
  it("defines lifecycle + tenant binding contract surface", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-sdk-contract.json")
    const contract = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(contract.version, "cicsc/phase6-sdk-contract-v1")
    assert.deepEqual(contract.surface.bundle_lifecycle, ["publishBundle", "resolveBundle"])
    assert.deepEqual(contract.surface.tenant_binding, ["bindTenant", "getTenantBinding", "listTenantBindingAudit"])
  })

  it("enforces bundle publish/bind/rebind with audit trail", async () => {
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
            commands: {},
            reducer: {},
          },
        },
      },
    }

    const pub = await publishBundle(fake.db as any, bundle)
    assert.ok(await resolveBundle(fake.db as any, pub.bundle_hash))

    await bindTenant(fake.db as any, { tenant_id: "tenant-a", bundle_hash: pub.bundle_hash, active_version: 0 })
    await bindTenant(fake.db as any, { tenant_id: "tenant-a", bundle_hash: pub.bundle_hash, active_version: 1 })
    const current = await getTenantBinding(fake.db as any, "tenant-a")
    assert.equal(current?.active_version, 1)

    const rows = await listTenantBindingAudit(fake.db as any, "tenant-a")
    assert.deepEqual(rows.map((r) => r.audit_id), [1, 2])
  })
})
