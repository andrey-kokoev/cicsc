import { describe, it } from "node:test"
import assert from "node:assert/strict"

import workerDefault from "../../runtime/http/worker"
import { putBundle } from "../../runtime/db/bundle-registry"
import { bindTenant } from "../../runtime/db/tenant-binding"

function makeFakeDb () {
  const bundles = new Map<string, string>()
  const bindings = new Map<string, { bundle_hash: string; active_version: number }>()
  const eventsByTenant = new Map<string, any[]>()

  return {
    eventsByTenant,
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
                if (sql.includes("SELECT active_version FROM tenant_versions")) {
                  const [tenant_id] = args
                  const b = bindings.get(String(tenant_id))
                  return { active_version: b?.active_version ?? 0 } as T
                }
                return null
              },
              async all<T = any> () {
                if (sql.includes("FROM events_v0")) {
                  const [tenant_id] = args
                  const rows = (eventsByTenant.get(String(tenant_id)) ?? []).slice()
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

describe("worker full-tenant verify", () => {
  it("verifies entire tenant history when entity stream is not specified", async () => {
    const fake = makeFakeDb()
    const bundle: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new", "open"],
            initial_state: "new",
            attrs: {},
            commands: {},
            reducer: {
              created: [{ set_state: { expr: { lit: { string: "open" } } } }],
            },
          },
        },
      },
    }

    const put = await putBundle(fake.db as any, bundle)
    await bindTenant(fake.db as any, { tenant_id: "t", bundle_hash: put.bundle_hash, active_version: 0 })

    fake.eventsByTenant.set("t", [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "A",
        seq: 1,
        event_type: "created",
        payload_json: "{}",
        ts: 1,
        actor_id: "u1",
      },
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "B",
        seq: 1,
        event_type: "created",
        payload_json: "{}",
        ts: 2,
        actor_id: "u2",
      },
    ])

    const res = await workerDefault.fetch(
      new Request("http://localhost/verify", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ tenant_id: "t" }),
      }),
      { DB: fake.db as any } as any
    )

    assert.equal(res.status, 200)
    const body = await res.json() as any
    assert.equal(body.ok, true)
    assert.equal(body.report.events_count, 2)
    assert.equal(body.report.entities_count, 2)
    assert.equal(body.report.version_stamp.tenant_id, "t")
    assert.equal(body.report.version_stamp.active_version, 0)
    assert.equal(typeof body.report.version_stamp.bundle_hash, "string")
  })
})
