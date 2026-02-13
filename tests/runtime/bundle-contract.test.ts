import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { publishBundle, resolveBundle, pinBundle, resolvePinnedBundle } from "../../runtime/db/bundle-contract"

function makeFakeDb () {
  const bundles = new Map<string, string>()
  const pins = new Map<string, string>()

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
                  return { success: true }
                }
                if (sql.includes("INSERT INTO bundle_pins")) {
                  const [pin_name, bundle_hash] = args
                  pins.set(String(pin_name), String(bundle_hash))
                  return { success: true }
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
                if (sql.includes("SELECT bundle_hash FROM bundle_pins")) {
                  const [pin_name] = args
                  const hash = pins.get(String(pin_name))
                  if (!hash) return null
                  return { bundle_hash: hash } as T
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

describe("bundle contract: publish/resolve/pin", () => {
  it("publishes and resolves bundle by hash", async () => {
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

    const out = await publishBundle(fake.db as any, bundle)
    const got = await resolveBundle(fake.db as any, out.bundle_hash)
    assert.ok(got)
    assert.deepEqual(got, bundle)
  })

  it("pins a hash and resolves pinned bundle", async () => {
    const fake = makeFakeDb()
    const bundleA: any = {
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
    const bundleB: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new", "open"],
            initial_state: "new",
            attrs: {},
            commands: { c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] } },
            reducer: {},
          },
        },
      },
    }

    const a = await publishBundle(fake.db as any, bundleA)
    const b = await publishBundle(fake.db as any, bundleB)

    await pinBundle(fake.db as any, "ticketing-stable", a.bundle_hash)
    let pinned = await resolvePinnedBundle(fake.db as any, "ticketing-stable")
    assert.ok(pinned)
    assert.equal(pinned?.bundle_hash, a.bundle_hash)

    await pinBundle(fake.db as any, "ticketing-stable", b.bundle_hash)
    pinned = await resolvePinnedBundle(fake.db as any, "ticketing-stable")
    assert.ok(pinned)
    assert.equal(pinned?.bundle_hash, b.bundle_hash)
    assert.deepEqual(pinned?.bundle, bundleB)
  })
})
