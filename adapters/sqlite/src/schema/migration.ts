import type { SchemaDiff } from "../../../../core/ir/diff"
import type { CoreIrV0 } from "../../../../core/ir/types"

export function generateSqlMigration (diff: SchemaDiff, params: {
  version: number
  nextVersion: number
}): string[] {
  const statements: string[] = []

  // If version changes, we likely create new tables and migrate data
  if (params.version !== params.nextVersion) {
    // This is handled by a higher level "re-eval" migration
    return []
  }

  // Same version, just column additions
  for (const [typeName, typeDiff] of Object.entries(diff.changedTypes)) {
    for (const field of typeDiff.addedFields) {
       // Note: Currently ALL shadow columns and attrs move into the snapshots table
       // but only shadow columns have their own SQL columns.
       // Regular attributes are in attrs_json.
    }
  }

  return statements
}
