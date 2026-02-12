import { describe, it } from "node:test"
import assert from "node:assert/strict"

import workerDefault from "../../runtime/http/worker"

function makeFakeDb () {
  const bundles = new Map<string, string>()

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
                return null
              },
            }
          },
        }
      },
    },
  }
}

describe("worker /bundle endpoint", () => {
  it("stores bundle and returns bundle_hash", async () => {
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
            commands: {
              c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] },
            },
            reducer: {},
          },
        },
      },
    }

    const res = await workerDefault.fetch(
      new Request("http://localhost/bundle", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify(bundle),
      }),
      { DB: fake.db as any } as any
    )

    assert.equal(res.status, 200)
    const body = await res.json() as any
    assert.equal(body.ok, true)
    assert.equal(typeof body.bundle_hash, "string")
    assert.equal(body.bundle_hash.length, 64)
  })

  it("retrieves stored bundle by hash", async () => {
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
            commands: {
              c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] },
            },
            reducer: {},
          },
        },
      },
    }

    const putRes = await workerDefault.fetch(
      new Request("http://localhost/bundle", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify(bundle),
      }),
      { DB: fake.db as any } as any
    )
    const putBody = await putRes.json() as any
    const hash = String(putBody.bundle_hash)

    const getRes = await workerDefault.fetch(
      new Request(`http://localhost/bundle/${encodeURIComponent(hash)}`),
      { DB: fake.db as any } as any
    )

    assert.equal(getRes.status, 200)
    const getBody = await getRes.json() as any
    assert.equal(getBody.ok, true)
    assert.deepEqual(getBody.bundle, bundle)
  })

  it("returns 404 for unknown bundle hash", async () => {
    const fake = makeFakeDb()
    const res = await workerDefault.fetch(
      new Request("http://localhost/bundle/not-found"),
      { DB: fake.db as any } as any
    )
    assert.equal(res.status, 404)
  })
})
