import type { CoreIrV0 } from "../../../core/ir/types"

export type SchemaGenOpts = {
  version: number
  schemaName?: string
}

export type SchemaGenOut = {
  sql: string
}

export function genPostgresSchemaFromIr (ir: CoreIrV0, opts: SchemaGenOpts): SchemaGenOut {
  const v = opts.version
  const schema = opts.schemaName ?? "public"

  const viewFields = collectIndexedFieldsFromViews(ir).filter((f) => f !== "attrs_json" && f !== "state")
  const viewIndexes = genSnapshotIndexes(schema, v, "view", viewFields)

  const constraintFields = collectIndexedFieldsFromConstraints(ir)
    .filter((f) => f !== "attrs_json" && f !== "state")
    .filter((f) => !viewFields.includes(f))
  const constraintIndexes = genSnapshotIndexes(schema, v, "constraint", constraintFields)

  const tables = [
    genTenantVersions(schema),
    genCommandReceipts(schema),
    genEventsTable(schema, v),
    genSnapshotsTable(ir, schema, v),
    viewIndexes,
    constraintIndexes,
  ]

  return { sql: tables.join("\n\n") }
}

function genSnapshotIndexes (schema: string, version: number, kind: "view" | "constraint", fields: string[]): string {
  if (fields.length === 0) return ""

  return fields
    .map((f) => {
      const safe = sanitizeIndexToken(f)
      return `
CREATE INDEX IF NOT EXISTS idx_snapshots_v${version}_${kind}_${safe}
  ON ${schema}.snapshots_v${version}(tenant_id, entity_type, ${escapeIdent(f)});
`.trim()
    })
    .join("\n\n")
}

function genTenantVersions (schema: string): string {
  return `
CREATE TABLE IF NOT EXISTS ${schema}.tenant_versions (
  tenant_id      TEXT PRIMARY KEY,
  active_version INTEGER NOT NULL
);
`.trim()
}

function genCommandReceipts (schema: string): string {
  return `
CREATE TABLE IF NOT EXISTS ${schema}.command_receipts (
  tenant_id    TEXT NOT NULL,
  command_id   TEXT NOT NULL,
  entity_type  TEXT NOT NULL,
  entity_id    TEXT NOT NULL,
  result_json  JSONB NOT NULL,
  ts           BIGINT NOT NULL,
  PRIMARY KEY (tenant_id, command_id)
);
`.trim()
}

function genEventsTable (schema: string, version: number): string {
  const tableName = `${schema}.events_v${version}`
  return `
CREATE TABLE IF NOT EXISTS ${tableName} (
  tenant_id    TEXT NOT NULL,
  entity_type  TEXT NOT NULL,
  entity_id    TEXT NOT NULL,
  seq          BIGINT NOT NULL,
  event_type   TEXT NOT NULL,
  payload_json JSONB NOT NULL,
  ts           BIGINT NOT NULL,
  actor_id     TEXT NOT NULL,
  PRIMARY KEY (tenant_id, entity_type, entity_id, seq)
);

CREATE INDEX IF NOT EXISTS idx_events_stream_v${version}
  ON ${tableName}(tenant_id, entity_type, entity_id, ts);

CREATE INDEX IF NOT EXISTS idx_events_type_time_v${version}
  ON ${tableName}(tenant_id, entity_type, event_type, ts);
`.trim()
}

function genSnapshotsTable (ir: CoreIrV0, schema: string, version: number): string {
  const shadowCols = collectShadowColumns(ir)
  const tableName = `${schema}.snapshots_v${version}`

  const cols = [
    `tenant_id   TEXT NOT NULL`,
    `entity_type TEXT NOT NULL`,
    `entity_id   TEXT NOT NULL`,
    `state       TEXT NOT NULL`,
    `attrs_json  JSONB NOT NULL`,
    `updated_ts  BIGINT NOT NULL`,
    ...shadowCols.map((c) => `  ${c.name} ${c.postgresType}`),
    `PRIMARY KEY (tenant_id, entity_type, entity_id)`,
  ]

  return `
CREATE TABLE IF NOT EXISTS ${tableName} (
${cols.map((c) => "  " + c).join(",\n")}
);

CREATE INDEX IF NOT EXISTS idx_snapshots_state_v${version}
  ON ${tableName}(tenant_id, entity_type, state);
`.trim()
}

type ShadowCol = {
  name: string
  postgresType: "BIGINT" | "TEXT" | "BOOLEAN" | "DOUBLE PRECISION" | "JSONB"
}

function collectShadowColumns (ir: CoreIrV0): ShadowCol[] {
  const out: Map<string, ShadowCol> = new Map()
  for (const t of Object.values(ir.types)) {
    for (const [name, s] of Object.entries(t.shadows ?? {})) {
      out.set(name, { name, postgresType: toPostgresType(s.type) })
    }
  }
  return Array.from(out.values())
}

function toPostgresType (t: string): ShadowCol["postgresType"] {
  switch (t) {
    case "int":
    case "time":
      return "BIGINT"
    case "bool":
      return "BOOLEAN"
    case "float":
      return "DOUBLE PRECISION"
    case "string":
    case "enum":
      return "TEXT"
    default:
      return "JSONB"
  }
}

function collectIndexedFieldsFromViews (ir: CoreIrV0): string[] {
  const out = new Set<string>()
  for (const view of Object.values(ir.views ?? {})) {
    const q: any = (view as any).query
    collectFieldsFromQuery(q, out)
  }
  return Array.from(out).sort()
}

function collectIndexedFieldsFromConstraints (ir: CoreIrV0): string[] {
  const out = new Set<string>()
  for (const c of Object.values(ir.constraints ?? {})) {
    if ((c as any).kind !== "bool_query") continue
    collectFieldsFromQuery((c as any).query, out)
  }
  return Array.from(out).sort()
}

function collectFieldsFromQuery (q: any, out: Set<string>): void {
  if (!q || typeof q !== "object") return
  const pipeline = Array.isArray(q.pipeline) ? q.pipeline : []
  for (const op of pipeline) {
    const tag = soleKey(op)
    const body = (op as any)[tag]
    if (tag === "filter") {
      collectFieldsFromExpr(body, out)
      continue
    }
    if (tag === "order_by") {
      const xs = Array.isArray(body) ? body : []
      for (const k of xs) collectFieldsFromExpr((k as any)?.expr, out)
      continue
    }
  }
}

function collectFieldsFromExpr (expr: any, out: Set<string>): void {
  if (!expr || typeof expr !== "object") return
  const tag = soleKey(expr)
  const body = (expr as any)[tag]

  if (tag === "ref") {
    const parts = (body as string).split(".")
    if (parts[0] === "shadow") out.add(parts[1]!)
    return
  }

  if (tag === "obj") {
    const fields = body?.fields ?? {}
    for (const v of Object.values(fields)) collectFieldsFromExpr(v, out)
    return
  }

  if (tag === "arr") {
    for (const x of (Array.isArray(body?.items) ? body.items : [])) collectFieldsFromExpr(x, out)
    return
  }

  if (tag === "map_enum") {
    collectFieldsFromExpr(body?.expr, out)
    return
  }

  if (tag === "call") {
    for (const a of (Array.isArray(body?.args) ? body.args : [])) collectFieldsFromExpr(a, out)
    return
  }
}

function escapeIdent (name: string): string {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new Error(`invalid column ident: ${name}`)
  return `"${name}"`
}

function sanitizeIndexToken (name: string): string {
  return name.replace(/[^A-Za-z0-9_]/g, "_")
}

function soleKey (o: any): string {
  const ks = Object.keys(o ?? {})
  if (ks.length !== 1) throw new Error("invalid tagged object")
  return ks[0]!
}
