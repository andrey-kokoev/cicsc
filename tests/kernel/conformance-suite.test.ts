import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { KernelMemoryBackend } from "../../kernel/src/memory-backend"
import { verifyHistoryAgainstIr } from "../../core/runtime/verify"
import type { VmIntrinsics } from "../../core/vm/eval"

const intrinsics: VmIntrinsics = {
  has_role: () => true,
  role_of: () => "user",
  auth_ok: () => true,
  constraint: () => true,
  len: () => 0,
  str: (v) => (v == null ? null : String(v)),
  int: () => null,
  float: () => null,
}

describe("kernel conformance suite", () => {
  it("replay verification over kernel memory backend produces deterministic pass", () => {
    const backend = new KernelMemoryBackend()
    backend.append([
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 1, event_type: "created", payload: {}, ts: 1, actor_id: "u" } as any,
    ])

    const bundle: any = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new", "open"],
            initial_state: "new",
            attrs: {},
            commands: {},
            reducer: { created: [{ set_state: { expr: { lit: { string: "open" } } } }] },
          },
        },
      },
    }

    const r1 = verifyHistoryAgainstIr({
      bundle,
      events: backend.readAll(),
      now: 2,
      actor: "u",
      intrinsics,
    })
    const r2 = verifyHistoryAgainstIr({
      bundle,
      events: backend.readAll(),
      now: 2,
      actor: "u",
      intrinsics,
    })

    assert.equal(r1.ok, true)
    assert.deepEqual(r1, r2)
  })
})
