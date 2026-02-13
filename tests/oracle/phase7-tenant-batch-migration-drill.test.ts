import { describe, it } from "node:test"
import assert from "node:assert/strict"

type TenantState = {
  tenantId: string
  version: number
  status: "active" | "paused"
}

function runBatchMigration(tenants: TenantState[], failTenantId: string | null): { final: TenantState[]; recovered: string[] } {
  const recovered: string[] = []
  const final = tenants.map((t) => ({ ...t, status: "paused" as const }))

  for (const t of final) {
    if (failTenantId && t.tenantId === failTenantId) {
      t.version = 1
      t.status = "active"
      recovered.push(t.tenantId)
      continue
    }
    t.version = 2
    t.status = "active"
  }

  return { final, recovered }
}

describe("phase7 tenant-batch migration drill", () => {
  it("migrates all tenants when no fault is injected", () => {
    const start: TenantState[] = [
      { tenantId: "t1", version: 1, status: "active" },
      { tenantId: "t2", version: 1, status: "active" },
      { tenantId: "t3", version: 1, status: "active" },
    ]

    const out = runBatchMigration(start, null)
    assert.deepEqual(out.recovered, [])
    assert.deepEqual(out.final.map((t) => t.version), [2, 2, 2])
    assert.deepEqual(out.final.map((t) => t.status), ["active", "active", "active"])
  })

  it("rolls back failed tenant deterministically and keeps others migrated", () => {
    const start: TenantState[] = [
      { tenantId: "t1", version: 1, status: "active" },
      { tenantId: "t2", version: 1, status: "active" },
      { tenantId: "t3", version: 1, status: "active" },
    ]

    const out = runBatchMigration(start, "t2")
    assert.deepEqual(out.recovered, ["t2"])
    assert.deepEqual(
      out.final.map((t) => ({ tenantId: t.tenantId, version: t.version, status: t.status })),
      [
        { tenantId: "t1", version: 2, status: "active" },
        { tenantId: "t2", version: 1, status: "active" },
        { tenantId: "t3", version: 2, status: "active" },
      ]
    )
  })
})
