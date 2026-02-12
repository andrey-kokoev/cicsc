import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { TenantTokenBucketLimiter } from "../../runtime/http/rate-limit"

describe("tenant rate limiter", () => {
  it("allows within capacity and rejects when depleted", () => {
    const l = new TenantTokenBucketLimiter(2, 0)
    assert.equal(l.check("t", 0).ok, true)
    assert.equal(l.check("t", 0).ok, true)
    const third = l.check("t", 0)
    assert.equal(third.ok, false)
    assert.equal(typeof third.retry_after_seconds, "number")
  })

  it("refills tokens over time", () => {
    const l = new TenantTokenBucketLimiter(1, 1) // 1 token/sec
    assert.equal(l.check("t", 0).ok, true)
    assert.equal(l.check("t", 0).ok, false)
    assert.equal(l.check("t", 1000).ok, true)
  })
})
