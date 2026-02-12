import { describe, it } from "node:test"
import assert from "node:assert/strict"

import workerDefault from "../../runtime/http/worker"
import { putBundle } from "../../runtime/db/bundle-registry"
import { getTenantBinding } from "../../runtime/db/tenant-binding"

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

describe("worker /bind endpoint", () => {
  it("binds tenant to stored bundle hash and version", async () => {
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

    const res = await workerDefault.fetch(
      new Request("http://localhost/bind", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ tenant_id: "t1", bundle_hash: put.bundle_hash, active_version: 2 }),
      }),
      { DB: fake.db as any } as any
    )

    assert.equal(res.status, 200)
    const body = await res.json() as any
    assert.equal(body.ok, true)

    const row = await getTenantBinding(fake.db as any, "t1")
    assert.deepEqual(row, { tenant_id: "t1", bundle_hash: put.bundle_hash, active_version: 2 })
  })

  it("returns 404 when binding unknown bundle hash", async () => {
    const fake = makeFakeDb()
    const res = await workerDefault.fetch(
      new Request("http://localhost/bind", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ tenant_id: "t1", bundle_hash: "nope", active_version: 0 }),
      }),
      { DB: fake.db as any } as any
    )

    assert.equal(res.status, 404)
  })

  it("enforces tenant bind auth when token configured", async () => {
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

    const denied = await workerDefault.fetch(
      new Request("http://localhost/bind", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ tenant_id: "t1", bundle_hash: put.bundle_hash, active_version: 0 }),
      }),
      { DB: fake.db as any, TENANT_BIND_TOKEN: "bind-secret" } as any
    )
    assert.equal(denied.status, 403)

    const allowed = await workerDefault.fetch(
      new Request("http://localhost/bind", {
        method: "POST",
        headers: { "content-type": "application/json", "x-cicsc-token": "bind-secret" },
        body: JSON.stringify({ tenant_id: "t1", bundle_hash: put.bundle_hash, active_version: 0 }),
      }),
      { DB: fake.db as any, TENANT_BIND_TOKEN: "bind-secret" } as any
    )
    assert.equal(allowed.status, 200)
  })
})
