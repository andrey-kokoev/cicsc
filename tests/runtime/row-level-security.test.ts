import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { applyRowLevelSecurity } from "../../runtime/view/rls"
import type { VmIntrinsics } from "../../core/vm/eval"

const intrinsics: VmIntrinsics = {
  has_role: (actor, role) => actor === role,
  role_of: (actor) => actor,
  auth_ok: () => true,
  constraint: () => true,
  len: () => null,
  str: (v) => (v == null ? null : String(v)),
  int: () => null,
  float: () => null,
}

describe("row-level security", () => {
  it("filters view rows by row_policy expression", () => {
    const rows = [
      { entity_id: "A", owner_id: "alice" },
      { entity_id: "B", owner_id: "bob" },
    ]

    const filtered = applyRowLevelSecurity({
      rows,
      actor_id: "alice",
      intrinsics,
      row_policy: {
        eq: [
          { var: { row: { field: "owner_id" } } },
          { var: { actor: true } },
        ],
      } as any,
    })

    assert.deepEqual(filtered, [{ entity_id: "A", owner_id: "alice" }])
  })
})
