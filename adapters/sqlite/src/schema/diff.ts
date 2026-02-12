import type { CoreIrV0 } from "../../../../core/ir/types"

export type SnapshotSchemaDiff = {
  statements: string[]
}

type SqlType = "INTEGER" | "REAL" | "TEXT"

export function genSnapshotsSchemaDiff (params: {
  previous: CoreIrV0
  next: CoreIrV0
  version: number
}): SnapshotSchemaDiff {
  const prev = collectShadowColumns(params.previous)
  const next = collectShadowColumns(params.next)

  const statements: string[] = []

  for (const [name, nextType] of next.entries()) {
    const prevType = prev.get(name)
    if (prevType == null) {
      statements.push(`ALTER TABLE snapshots_v${params.version} ADD COLUMN ${escapeIdent(name)} ${nextType};`)
      continue
    }
    if (prevType !== nextType) {
      throw new Error(
        `snapshot schema diff: incompatible shadow type change for '${name}' (${prevType} -> ${nextType})`
      )
    }
  }

  return { statements }
}

function collectShadowColumns (ir: CoreIrV0): Map<string, SqlType> {
  const out = new Map<string, SqlType>()
  for (const t of Object.values(ir.types ?? {})) {
    const shadows = (t as any).shadows ?? {}
    for (const [name, def] of Object.entries(shadows)) {
      const next = toSqliteType((def as any).type)
      const prev = out.get(name)
      if (prev == null) out.set(name, next)
      else if (prev !== next) {
        throw new Error(`snapshot schema diff: inconsistent shadow type for '${name}' in input IR`)
      }
    }
  }
  return out
}

function toSqliteType (t: string): SqlType {
  switch (t) {
    case "int":
    case "time":
    case "bool":
      return "INTEGER"
    case "float":
      return "REAL"
    case "string":
    case "enum":
    default:
      return "TEXT"
  }
}

function escapeIdent (name: string): string {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new Error(`invalid column ident: ${name}`)
  return `"${name}"`
}
