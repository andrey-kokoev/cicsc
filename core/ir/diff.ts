import type { CoreIrV0, EntityTypeSpecV0 } from "./types"

export type SchemaDiff = {
  addedTypes: string[]
  removedTypes: string[]
  changedTypes: Record<string, TypeDiff>
  classification: "safe" | "dangerous" | "breaking"
}

export type TypeDiff = {
  addedFields: string[]
  removedFields: string[]
  changedFields: Record<string, FieldDiff>
  addedStates: string[]
  removedStates: string[]
  dataLoss: boolean
}

export type FieldDiff = {
  oldType: string | undefined
  newType: string | undefined
}

export function diffCoreIr (from: CoreIrV0, to: CoreIrV0): SchemaDiff {
  const addedTypes = Object.keys(to.types).filter(t => !from.types[t])
  const removedTypes = Object.keys(from.types).filter(t => !to.types[t])
  const changedTypes: Record<string, TypeDiff> = {}

  let classification: "safe" | "dangerous" | "breaking" = "safe"

  if (removedTypes.length > 0) classification = "breaking"

  for (const typeName of Object.keys(from.types)) {
    if (to.types[typeName]) {
      const diff = diffEntityType(from.types[typeName], to.types[typeName])
      if (hasChanges(diff)) {
        changedTypes[typeName] = diff
        if (diff.removedFields.length > 0 || Object.keys(diff.changedFields).length > 0 || diff.removedStates.length > 0) {
          classification = "breaking"
        } else if (diff.addedFields.some(f => !to.types[typeName].attrs[f].optional)) {
          classification = "dangerous" // Non-optional field addition
        }
      }
    }
  }

  return { addedTypes, removedTypes, changedTypes, classification }
}

export function formatDiff (diff: SchemaDiff): string {
  const lines: string[] = []
  lines.push(`Classification: ${diff.classification.toUpperCase()}`)

  if (diff.addedTypes.length) lines.push(`Added Types: ${diff.addedTypes.join(", ")}`)
  if (diff.removedTypes.length) lines.push(`Removed Types: ${diff.removedTypes.join(", ")}`)

  for (const [typeName, typeDiff] of Object.entries(diff.changedTypes)) {
    lines.push(`\nType ${typeName}:`)
    if (typeDiff.addedFields.length) lines.push(`  + Fields: ${typeDiff.addedFields.join(", ")}`)
    if (typeDiff.removedFields.length) lines.push(`  - Fields: ${typeDiff.removedFields.join(", ")}`)
    for (const [f, fd] of Object.entries(typeDiff.changedFields)) {
      lines.push(`  * Field ${f}: ${fd.oldType} -> ${fd.newType}`)
    }
  }

  return lines.join("\n")
}

function diffEntityType (from: EntityTypeSpecV0, to: EntityTypeSpecV0): TypeDiff {
  const addedFields = Object.keys(to.attrs).filter(f => !from.attrs[f])
  const removedFields = Object.keys(from.attrs).filter(f => !to.attrs[f])
  const changedFields: Record<string, FieldDiff> = {}

  for (const fieldName of Object.keys(from.attrs)) {
    if (to.attrs[fieldName]) {
      if (from.attrs[fieldName].type !== to.attrs[fieldName].type) {
        changedFields[fieldName] = {
          oldType: from.attrs[fieldName].type,
          newType: to.attrs[fieldName].type
        }
      }
    }
  }

  const addedStates = to.states.filter(s => !from.states.includes(s))
  const removedStates = from.states.filter(s => !to.states.includes(s))

  const dataLoss = removedFields.length > 0 || Object.keys(changedFields).length > 0 || removedStates.length > 0

  return { addedFields, removedFields, changedFields, addedStates, removedStates, dataLoss }
}

function hasChanges (diff: TypeDiff): boolean {
  return diff.addedFields.length > 0 ||
    diff.removedFields.length > 0 ||
    Object.keys(diff.changedFields).length > 0 ||
    diff.addedStates.length > 0 ||
    diff.removedStates.length > 0
}
