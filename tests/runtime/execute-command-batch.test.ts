import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { executeCommandBatchTx } from "../../runtime/execute-command-batch"

describe("batched command execution", () => {
  it("executes commands sequentially", async () => {
    const order: string[] = []
    const out = await executeCommandBatchTx({
      ir: { version: 0, types: {} } as any,
      store: { adapter: {} },
      intrinsics: {} as any,
      requests: [
        { command_id: "c1" } as any,
        { command_id: "c2" } as any,
      ],
      executeOne: async ({ req }) => {
        order.push(String((req as any).command_id))
        return { command_id: (req as any).command_id } as any
      },
    })

    assert.equal(out.ok, true)
    assert.deepEqual(order, ["c1", "c2"])
    assert.equal(out.results.length, 2)
  })

  it("stops on first error by default", async () => {
    const order: string[] = []
    const out = await executeCommandBatchTx({
      ir: { version: 0, types: {} } as any,
      store: { adapter: {} },
      intrinsics: {} as any,
      requests: [{ command_id: "ok" } as any, { command_id: "bad" } as any, { command_id: "later" } as any],
      executeOne: async ({ req }) => {
        const id = String((req as any).command_id)
        order.push(id)
        if (id === "bad") throw new Error("boom")
        return { command_id: id } as any
      },
    })

    assert.equal(out.ok, false)
    assert.deepEqual(order, ["ok", "bad"])
    assert.equal(out.results.length, 2)
    assert.equal(out.results[1]!.ok, false)
  })
})
