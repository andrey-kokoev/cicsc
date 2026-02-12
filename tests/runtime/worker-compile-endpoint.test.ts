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

describe("worker /compile endpoint", () => {
  it("compiles spec and persists resulting bundle", async () => {
    const fake = makeFakeDb()
    const spec = {
      version: 0,
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

    const compileRes = await workerDefault.fetch(
      new Request("http://localhost/compile", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify(spec),
      }),
      { DB: fake.db as any } as any
    )
    assert.equal(compileRes.status, 200)
    const compileBody = await compileRes.json() as any
    assert.equal(compileBody.ok, true)
    assert.equal(typeof compileBody.bundle_hash, "string")

    const getRes = await workerDefault.fetch(
      new Request(`http://localhost/bundle/${encodeURIComponent(String(compileBody.bundle_hash))}`),
      { DB: fake.db as any } as any
    )
    assert.equal(getRes.status, 200)
    const getBody = await getRes.json() as any
    assert.equal(getBody.ok, true)
    assert.equal(getBody.bundle.core_ir.version, 0)
  })
})
