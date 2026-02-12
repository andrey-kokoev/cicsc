import { describe, it } from "node:test"
import assert from "node:assert/strict"

import workerDefault from "../../runtime/http/worker"
import { loadTenantBundle } from "../../runtime/http/tenant-bundle"

function makeFakeDb () {
  const bundles = new Map<string, string>()
  const bindings = new Map<string, { bundle_hash: string; active_version: number }>()
  const tenantVersions = new Map<string, number>()

  function firstBySql<T> (sql: string, args: any[]): T | null {
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
      return { active_version: tenantVersions.get(String(tenant_id)) ?? 0 } as T
    }
    return null
  }

  function runBySql (sql: string, args: any[]) {
    if (sql.includes("INSERT INTO bundle_registry")) {
      const [hash, json] = args
      if (!bundles.has(String(hash))) bundles.set(String(hash), String(json))
    } else if (sql.includes("INSERT INTO tenant_bindings")) {
      const [tenant_id, bundle_hash, active_version] = args
      bindings.set(String(tenant_id), {
        bundle_hash: String(bundle_hash),
        active_version: Number(active_version),
      })
    } else if (sql.includes("INSERT INTO tenant_versions")) {
      const [tenant_id, active_version] = args
      tenantVersions.set(String(tenant_id), Number(active_version))
    }
  }

  const db = {
    async exec (_sql: string) {
      return { ok: true }
    },
    prepare (sql: string) {
      return {
        bind (...args: any[]) {
          const stmt = {
            sql,
            args,
            async run () {
              runBySql(sql, args)
              return { success: true }
            },
            async first<T = any> () {
              return firstBySql<T>(sql, args)
            },
            async all<T = any> () {
              return { results: [] as T[] }
            },
          }
          return stmt
        },
      }
    },
    async batch (stmts: any[]) {
      const out: any[] = []
      for (const s of stmts) {
        const sql = String(s?.sql ?? "")
        const args = (s?.args ?? []) as any[]
        if (sql.trim().toUpperCase().startsWith("SELECT")) {
          const row = firstBySql<any>(sql, args)
          out.push({ success: true, results: row ? [row] : [] })
        } else {
          runBySql(sql, args)
          out.push({ success: true, results: [] })
        }
      }
      return out
    },
  }

  return { db, tenantVersions }
}

describe("worker /install-from-spec endpoint", () => {
  it("compiles, persists, binds tenant, and activates version", async () => {
    const fake = makeFakeDb()
    const spec = {
      version: 0,
      tenant_id: "t-install",
      entities: {
        Ticket: {
          id: "string",
          states: ["new"],
          initial: "new",
          commands: {
            create: { emit: [{ type: "created", payload: {} }] },
          },
          reducers: {
            created: [{ set_state: "new" }],
          },
        },
      },
    }

    const res = await workerDefault.fetch(
      new Request("http://localhost/install-from-spec", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify(spec),
      }),
      { DB: fake.db as any } as any
    )
    assert.equal(res.status, 200)
    const body = await res.json() as any
    assert.equal(body.ok, true)
    assert.equal(body.tenant_id, "t-install")
    assert.equal(body.active_version, 0)
    assert.equal(typeof body.bundle_hash, "string")

    const loaded = await loadTenantBundle(fake.db as any, "t-install")
    assert.equal(loaded.bundle_hash, body.bundle_hash)
    assert.equal(loaded.active_version, 0)
    assert.equal(fake.tenantVersions.get("t-install"), 0)
  })
})
