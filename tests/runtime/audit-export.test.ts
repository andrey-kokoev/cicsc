import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { exportAuditLog } from "../../runtime/audit/export"

describe("audit export", () => {
  it("exports NDJSON records", () => {
    const out = exportAuditLog({
      format: "ndjson",
      records: [
        { ts: 1, tenant_id: "t", kind: "event", payload: { event_type: "created" } },
        { ts: 2, tenant_id: "t", kind: "verify", payload: { ok: true } },
      ],
    })

    assert.equal(out.mime, "application/x-ndjson")
    assert.equal(typeof out.body, "string")
    const text = out.body as string
    assert.equal(text.split("\n").length, 2)
    assert.match(text, /"kind":"event"/)
  })

  it("exports parquet when encoder is provided", () => {
    const out = exportAuditLog({
      format: "parquet",
      records: [{ ts: 1, tenant_id: "t", kind: "event", payload: {} }],
      parquetEncode: () => new Uint8Array([1, 2, 3]),
    })

    assert.equal(out.mime, "application/vnd.apache.parquet")
    assert.deepEqual(out.body, new Uint8Array([1, 2, 3]))
  })

  it("fails parquet export when encoder is missing", () => {
    assert.throws(
      () =>
        exportAuditLog({
          format: "parquet",
          records: [],
        }),
      /no parquet encoder/
    )
  })
})
