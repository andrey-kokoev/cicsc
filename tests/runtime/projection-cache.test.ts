import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { ProjectionCache } from "../../runtime/cache/projection-cache"

describe("projection cache", () => {
  it("stores and retrieves cached projections", () => {
    const c = new ProjectionCache(10)
    c.set(
      { tenant_id: "t", view_name: "board", args_hash: "a" },
      { rows: [{ id: 1 }], computed_at: 1 }
    )
    const got = c.get({ tenant_id: "t", view_name: "board", args_hash: "a" })
    assert.ok(got)
    assert.deepEqual(got?.rows, [{ id: 1 }])
  })

  it("evicts oldest entries when max size is exceeded", () => {
    const c = new ProjectionCache(2)
    c.set({ tenant_id: "t", view_name: "v1", args_hash: "a" }, { rows: [], computed_at: 1 })
    c.set({ tenant_id: "t", view_name: "v2", args_hash: "a" }, { rows: [], computed_at: 2 })
    c.set({ tenant_id: "t", view_name: "v3", args_hash: "a" }, { rows: [], computed_at: 3 })

    assert.equal(c.get({ tenant_id: "t", view_name: "v1", args_hash: "a" }), null)
    assert.equal(c.size(), 2)
  })

  it("invalidates all cache entries for a tenant", () => {
    const c = new ProjectionCache(10)
    c.set({ tenant_id: "t1", view_name: "v", args_hash: "a" }, { rows: [], computed_at: 1 })
    c.set({ tenant_id: "t2", view_name: "v", args_hash: "a" }, { rows: [], computed_at: 1 })
    c.invalidateTenant("t1")
    assert.equal(c.get({ tenant_id: "t1", view_name: "v", args_hash: "a" }), null)
    assert.ok(c.get({ tenant_id: "t2", view_name: "v", args_hash: "a" }))
  })
})
