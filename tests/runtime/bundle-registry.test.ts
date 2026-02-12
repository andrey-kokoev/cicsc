import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { bundleHash, getBundle, putBundle } from "../../runtime/db/bundle-registry"

function makeFakeDb () {
  const map = new Map<string, string>()

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
                  if (!map.has(String(hash))) map.set(String(hash), String(json))
                  return { success: true }
                }
                return { success: true }
              },
              async first<T = any> () {
                if (sql.includes("SELECT bundle_json FROM bundle_registry")) {
                  const [hash] = args
                  const json = map.get(String(hash))
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

describe("bundle registry", () => {
  it("stores and retrieves bundles by deterministic hash", async () => {
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

    const put = await putBundle(fake.db as any, bundle)
    const got = await getBundle(fake.db as any, put.bundle_hash)
    assert.ok(got)
    assert.deepEqual(got, bundle)
  })

  it("produces same hash for semantically equal bundles with different key order", () => {
    const a: any = {
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

    const b: any = {
      core_ir: {
        types: {
          Ticket: {
            reducer: {},
            commands: { c: { emits: [], guard: { expr: { lit: { bool: true } } }, input: {} } },
            attrs: {},
            initial_state: "new",
            states: ["new"],
            id_type: "string",
          },
        },
        version: 0,
      },
    }

    assert.equal(bundleHash(a), bundleHash(b))
  })
})
