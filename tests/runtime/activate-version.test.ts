import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { activateVersion } from "../../runtime/db/activate-version"
import type { CoreIrV0 } from "../../core/ir/types"

describe("version activation", () => {
  it("installs schema before setting active version", async () => {
    const calls: string[] = []

    const db = {
      async exec (_sql: string) {
        calls.push("install")
      },
    }

    const setActiveVersion = async (_tenant_id: string, _version: number) => {
      calls.push("activate")
    }

    const ir: CoreIrV0 = {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new"],
          initial_state: "new",
          attrs: {},
          commands: {
            c: { input: {}, guard: { expr: { lit: { bool: true } } as any }, emits: [] },
          },
          reducer: {},
        },
      },
    }

    await activateVersion({
      db,
      ir,
      version: 1,
      tenant_id: "t",
      setActiveVersion,
    })

    assert.deepEqual(calls, ["install", "activate"])
  })
})
