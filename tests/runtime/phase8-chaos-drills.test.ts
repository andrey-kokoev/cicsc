import { describe, it } from "node:test"
import assert from "node:assert/strict"

type Tenant = { id: string; healthy: boolean; backlog: number; verifyLagMs: number }

function simulateOutage(tenants: Tenant[], tenantId: string): Tenant[] {
  return tenants.map((t) => (t.id === tenantId ? { ...t, healthy: false } : { ...t }))
}

function simulateVerifyDelay(tenants: Tenant[], tenantId: string, lagMs: number): Tenant[] {
  return tenants.map((t) => (t.id === tenantId ? { ...t, verifyLagMs: lagMs } : { ...t }))
}

function simulateReplayBackpressure(tenants: Tenant[], tenantId: string, backlog: number): Tenant[] {
  return tenants.map((t) => (t.id === tenantId ? { ...t, backlog } : { ...t }))
}

describe("phase8 multi-tenant chaos drills", () => {
  it("contains partial outage to target tenant without global spillover", () => {
    const tenants: Tenant[] = [
      { id: "t1", healthy: true, backlog: 0, verifyLagMs: 0 },
      { id: "t2", healthy: true, backlog: 0, verifyLagMs: 0 },
    ]
    const out = simulateOutage(tenants, "t2")
    assert.equal(out.find((t) => t.id === "t1")?.healthy, true)
    assert.equal(out.find((t) => t.id === "t2")?.healthy, false)
  })

  it("tracks verify delay without breaking unrelated tenant state", () => {
    const tenants: Tenant[] = [
      { id: "t1", healthy: true, backlog: 0, verifyLagMs: 0 },
      { id: "t2", healthy: true, backlog: 0, verifyLagMs: 0 },
    ]
    const out = simulateVerifyDelay(tenants, "t1", 120000)
    assert.equal(out.find((t) => t.id === "t1")?.verifyLagMs, 120000)
    assert.equal(out.find((t) => t.id === "t2")?.verifyLagMs, 0)
  })

  it("models replay backpressure as tenant-scoped queue growth", () => {
    const tenants: Tenant[] = [
      { id: "t1", healthy: true, backlog: 0, verifyLagMs: 0 },
      { id: "t2", healthy: true, backlog: 0, verifyLagMs: 0 },
    ]
    const out = simulateReplayBackpressure(tenants, "t2", 5000)
    assert.equal(out.find((t) => t.id === "t1")?.backlog, 0)
    assert.equal(out.find((t) => t.id === "t2")?.backlog, 5000)
  })
})
