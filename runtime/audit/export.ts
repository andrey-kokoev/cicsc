export type AuditRecord = {
  ts: number
  tenant_id: string
  kind: "event" | "snapshot" | "verify" | "policy"
  payload: Record<string, unknown>
}

export type AuditExportFormat = "ndjson" | "parquet"

export function exportAuditLog (params: {
  records: AuditRecord[]
  format: AuditExportFormat
  parquetEncode?: (records: AuditRecord[]) => Uint8Array
}): { mime: string; body: string | Uint8Array } {
  if (params.format === "ndjson") {
    return {
      mime: "application/x-ndjson",
      body: exportNdjson(params.records),
    }
  }

  if (!params.parquetEncode) {
    throw new Error("parquet export requested but no parquet encoder is configured")
  }

  return {
    mime: "application/vnd.apache.parquet",
    body: params.parquetEncode(params.records),
  }
}

export function exportNdjson (records: AuditRecord[]): string {
  return records
    .map((r) => JSON.stringify({
      ts: r.ts,
      tenant_id: r.tenant_id,
      kind: r.kind,
      payload: r.payload,
    }))
    .join("\n")
}
