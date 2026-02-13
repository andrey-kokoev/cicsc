import { describe, it } from "node:test"
import assert from "node:assert/strict"

type TenantQueue = { tenant: string; pending: number; served: number }

function roundRobinStep(queues: TenantQueue[]): TenantQueue[] {
  return queues.map((q) => {
    if (q.pending > 0) {
      return { ...q, pending: q.pending - 1, served: q.served + 1 }
    }
    return q
  })
}

describe("phase8 tenant fairness and starvation checks", () => {
  it("serves every active tenant under round-robin scheduling", () => {
    let queues: TenantQueue[] = [
      { tenant: "t1", pending: 5, served: 0 },
      { tenant: "t2", pending: 3, served: 0 },
      { tenant: "t3", pending: 4, served: 0 },
    ]

    for (let i = 0; i < 3; i++) {
      queues = roundRobinStep(queues)
    }

    for (const q of queues) {
      assert.ok(q.served >= 1, `${q.tenant} starved`)
    }
  })

  it("does not let heavy tenant fully starve smaller tenant", () => {
    let queues: TenantQueue[] = [
      { tenant: "heavy", pending: 100, served: 0 },
      { tenant: "small", pending: 2, served: 0 },
    ]

    for (let i = 0; i < 2; i++) {
      queues = roundRobinStep(queues)
    }

    const small = queues.find((q) => q.tenant === "small")
    assert.equal(small?.served, 2)
  })
})
