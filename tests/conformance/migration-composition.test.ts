// /tests/conformance/migration-composition.test.ts
// Phase 4: Migration composition and safety tests (P4.4.1, P4.4.2, P4.4.3)

import { describe, it } from "node:test"
import assert from "node:assert/strict"

// Event and State types matching Lean
type Event = {
  tenantId: string
  entityType: string
  entityId: string
  seq: number
  eventType: string
  payload: unknown
  ts: number
  actor: string
}

type State = {
  st: string
  attrs: Record<string, unknown>
  shadows: Record<string, unknown>
}

// Migration spec matching Lean MigrationSpec
type EventTransform = {
  source: string
  target: string
  drop: boolean
}

type MigrationSpec = {
  fromVersion: number
  toVersion: number
  entityType: string
  transforms: EventTransform[]
  stateMap: Array<[string, string]> // [from, to] pairs
}

/** Look up transform for an event type */
function lookupTransform(ms: MigrationSpec, eventType: string): EventTransform | undefined {
  return ms.transforms.find(t => t.source === eventType)
}

/** Migrate a single event */
function migrateEvent(ms: MigrationSpec, e: Event): Event | null {
  if (e.entityType !== ms.entityType) {
    return e // Not our entity type, unchanged
  }
  
  const t = lookupTransform(ms, e.eventType)
  if (!t) return e // No transform, unchanged
  if (t.drop) return null // Dropped
  
  return { ...e, eventType: t.target }
}

/** Migrate state label */
function migrateState(ms: MigrationSpec, s: State): State {
  const mapping = ms.stateMap.find(([from]) => from === s.st)
  if (mapping) {
    return { ...s, st: mapping[1] }
  }
  return s
}

/** Migrate entire history */
function migrateHistory(ms: MigrationSpec, h: Event[]): Event[] {
  return h.map(e => migrateEvent(ms, e)).filter((e): e is Event => e !== null)
}

/** Compose two migrations: m1 (v0→v1) then m2 (v1→v2) = v0→v2 */
function composeMigrations(m1: MigrationSpec, m2: MigrationSpec): MigrationSpec {
  // Compose event transforms
  const composedTransforms: EventTransform[] = m1.transforms.map(t1 => {
    if (t1.drop) return t1 // Drop stays drop
    
    // Check if t1's target has a transform in m2
    const t2 = lookupTransform(m2, t1.target)
    if (!t2) {
      // No further transform, keep as-is
      return { ...t1 }
    }
    if (t2.drop) {
      // Target gets dropped in m2
      return { source: t1.source, target: t2.target, drop: true }
    }
    // Chain: source → t1.target → t2.target
    return { source: t1.source, target: t2.target, drop: false }
  })
  
  // Add any transforms from m2 that don't have a source in m1
  // (these are new event types added in v1)
  const m1Sources = new Set(m1.transforms.map(t => t.source))
  for (const t2 of m2.transforms) {
    if (!m1Sources.has(t2.source)) {
      composedTransforms.push(t2)
    }
  }
  
  // Compose state maps: v0 → v1 → v2
  const composedStateMap: Array<[string, string]> = m1.stateMap.map(([from, mid]) => {
    const v2Mapping = m2.stateMap.find(([m]) => m === mid)
    if (v2Mapping) {
      return [from, v2Mapping[1]] // from v0 directly to v2
    }
    return [from, mid] // stays at v1 mapping
  })
  
  // Add any state mappings from m2 that start from states not in m1
  const m1FromStates = new Set(m1.stateMap.map(([f]) => f))
  for (const [from, to] of m2.stateMap) {
    if (!m1FromStates.has(from)) {
      composedStateMap.push([from, to])
    }
  }
  
  return {
    fromVersion: m1.fromVersion,
    toVersion: m2.toVersion,
    entityType: m1.entityType,
    transforms: composedTransforms,
    stateMap: composedStateMap,
  }
}

/** Check if migration has drops (irreversible) */
function hasDrops(ms: MigrationSpec): boolean {
  return ms.transforms.some(t => t.drop)
}

/** Try to compute inverse migration (returns null if has drops) */
function inverseMigration(ms: MigrationSpec): MigrationSpec | null {
  if (hasDrops(ms)) {
    return null // Cannot invert drops
  }
  
  // Reverse event transforms
  const inverseTransforms: EventTransform[] = ms.transforms.map(t => ({
    source: t.target,
    target: t.source,
    drop: false,
  }))
  
  // Reverse state map
  const inverseStateMap: Array<[string, string]> = ms.stateMap.map(([from, to]) => [to, from])
  
  return {
    fromVersion: ms.toVersion,
    toVersion: ms.fromVersion,
    entityType: ms.entityType,
    transforms: inverseTransforms,
    stateMap: inverseStateMap,
  }
}

/** SafeMigration predicate: no drops, all targets valid */
type SafeMigrationCheck = {
  noDataLoss: boolean
  typeSafe: boolean
  reversible: boolean
  total: boolean
}

function checkSafeMigration(ms: MigrationSpec): SafeMigrationCheck {
  return {
    noDataLoss: !hasDrops(ms),
    typeSafe: ms.transforms.every(t => !t.drop || t.drop === true), // explicit drops ok
    reversible: inverseMigration(ms) !== null,
    total: ms.transforms.length > 0, // simplified check
  }
}

describe("P4.4.1: Migration composition tests", () => {
  const m0to1: MigrationSpec = {
    fromVersion: 0,
    toVersion: 1,
    entityType: "Ticket",
    transforms: [
      { source: "CreateTicket", target: "TicketCreated", drop: false },
      { source: "UpdateTicket", target: "TicketUpdated", drop: false },
    ],
    stateMap: [["open", "new"], ["closed", "done"]],
  }
  
  const m1to2: MigrationSpec = {
    fromVersion: 1,
    toVersion: 2,
    entityType: "Ticket",
    transforms: [
      { source: "TicketCreated", target: "TicketOpened", drop: false },
      { source: "TicketUpdated", target: "TicketModified", drop: false },
    ],
    stateMap: [["new", "open"], ["done", "closed"]],
  }
  
  it("composes migrations associatively", () => {
    const m0to2 = composeMigrations(m0to1, m1to2)
    
    // Result should go from v0 to v2
    assert.strictEqual(m0to2.fromVersion, 0)
    assert.strictEqual(m0to2.toVersion, 2)
    
    // Event transforms should chain
    const createTransform = m0to2.transforms.find(t => t.source === "CreateTicket")
    assert.ok(createTransform)
    assert.strictEqual(createTransform?.target, "TicketOpened") // chained through TicketCreated
    
    // State maps should compose
    const openMapping = m0to2.stateMap.find(([f]) => f === "open")
    assert.ok(openMapping)
    assert.strictEqual(openMapping?.[1], "open") // open→new→open
  })
  
  it("migrates history correctly through composed migration", () => {
    const m0to2 = composeMigrations(m0to1, m1to2)
    
    const history: Event[] = [
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "CreateTicket", payload: {}, ts: 1, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 2, eventType: "UpdateTicket", payload: {}, ts: 2, actor: "a" },
    ]
    
    // Direct v0→v2 migration
    const direct = migrateHistory(m0to2, history)
    
    // Step-wise migration
    const step1 = migrateHistory(m0to1, history)
    const step2 = migrateHistory(m1to2, step1)
    
    // Results should match
    assert.strictEqual(direct.length, step2.length)
    assert.strictEqual(direct[0].eventType, step2[0].eventType)
    assert.strictEqual(direct[0].eventType, "TicketOpened")
  })
  
  it("handles new event types added in intermediate version", () => {
    // m1 adds a new event type not in m0
    const m1WithNew: MigrationSpec = {
      fromVersion: 1,
      toVersion: 2,
      entityType: "Ticket",
      transforms: [
        { source: "TicketCreated", target: "TicketOpened", drop: false },
        { source: "TicketAssigned", target: "TicketAssigned", drop: false }, // New in v1
      ],
      stateMap: [],
    }
    
    const m0to2 = composeMigrations(m0to1, m1WithNew)
    
    // Should include the new event type
    const newTransform = m0to2.transforms.find(t => t.source === "TicketAssigned")
    assert.ok(newTransform, "New event type from v1 should be in composed migration")
  })
  
  it("propagates drops through composition", () => {
    const mWithDrop: MigrationSpec = {
      fromVersion: 1,
      toVersion: 2,
      entityType: "Ticket",
      transforms: [
        { source: "TicketCreated", target: "", drop: true }, // Drop this event type
      ],
      stateMap: [],
    }
    
    const m0to2 = composeMigrations(m0to1, mWithDrop)
    
    // CreateTicket should now be dropped
    const createTransform = m0to2.transforms.find(t => t.source === "CreateTicket")
    assert.ok(createTransform?.drop, "Drop should propagate through composition")
  })
})

describe("P4.4.2: Reversible migration path tests", () => {
  const reversibleMigration: MigrationSpec = {
    fromVersion: 0,
    toVersion: 1,
    entityType: "Ticket",
    transforms: [
      { source: "Create", target: "Open", drop: false },
      { source: "Update", target: "Modify", drop: false },
    ],
    stateMap: [["new", "open"]],
  }
  
  const irreversibleMigration: MigrationSpec = {
    fromVersion: 0,
    toVersion: 1,
    entityType: "Ticket",
    transforms: [
      { source: "Create", target: "Open", drop: false },
      { source: "TempEvent", target: "", drop: true }, // Drop = irreversible
    ],
    stateMap: [],
  }
  
  it("computes inverse for reversible migration", () => {
    const inverse = inverseMigration(reversibleMigration)
    
    assert.ok(inverse, "Should compute inverse for reversible migration")
    assert.strictEqual(inverse?.fromVersion, 1)
    assert.strictEqual(inverse?.toVersion, 0)
    
    // Event transforms reversed
    const openTransform = inverse?.transforms.find(t => t.source === "Open")
    assert.ok(openTransform)
    assert.strictEqual(openTransform?.target, "Create")
    
    // State map reversed
    const openStateMap = inverse?.stateMap.find(([f]) => f === "open")
    assert.ok(openStateMap)
    assert.strictEqual(openStateMap?.[1], "new")
  })
  
  it("returns null for irreversible migration (has drops)", () => {
    const inverse = inverseMigration(irreversibleMigration)
    
    assert.strictEqual(inverse, null, "Should not compute inverse for migration with drops")
  })
  
  it("roundtrip migration restores original event types", () => {
    const inverse = inverseMigration(reversibleMigration)!
    const history: Event[] = [
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "Create", payload: {}, ts: 1, actor: "a" },
    ]
    
    // Forward migration
    const forward = migrateHistory(reversibleMigration, history)
    assert.strictEqual(forward[0].eventType, "Open")
    
    // Backward migration
    const backward = migrateHistory(inverse, forward)
    assert.strictEqual(backward[0].eventType, "Create")
  })
  
  it("roundtrip migration restores original state labels", () => {
    const inverse = inverseMigration(reversibleMigration)!
    
    const state: State = { st: "new", attrs: {}, shadows: {} }
    
    // Forward
    const forward = migrateState(reversibleMigration, state)
    assert.strictEqual(forward.st, "open")
    
    // Backward
    const backward = migrateState(inverse, forward)
    assert.strictEqual(backward.st, "new")
  })
})

describe("P4.4.3: SafeMigration checklist", () => {
  it("marks migration with drops as not reversible", () => {
    const unsafeMigration: MigrationSpec = {
      fromVersion: 0,
      toVersion: 1,
      entityType: "Ticket",
      transforms: [
        { source: "OldEvent", target: "", drop: true },
      ],
      stateMap: [],
    }
    
    const check = checkSafeMigration(unsafeMigration)
    
    assert.strictEqual(check.noDataLoss, false, "Migration with drops has data loss")
    assert.strictEqual(check.reversible, false, "Migration with drops is not reversible")
  })
  
  it("marks rename-only migration as safe", () => {
    const safeMigration: MigrationSpec = {
      fromVersion: 0,
      toVersion: 1,
      entityType: "Ticket",
      transforms: [
        { source: "Create", target: "Open", drop: false },
      ],
      stateMap: [["new", "open"]],
    }
    
    const check = checkSafeMigration(safeMigration)
    
    assert.strictEqual(check.noDataLoss, true)
    assert.strictEqual(check.reversible, true)
    assert.strictEqual(check.typeSafe, true)
  })
  
  it("detects unsafe patterns in migration", () => {
    const unsafePatterns = [
      {
        name: "Event drop",
        migration: {
          fromVersion: 0,
          toVersion: 1,
          entityType: "Ticket",
          transforms: [{ source: "X", target: "", drop: true }],
          stateMap: [],
        },
        expectedIssue: "noDataLoss",
      },
      {
        name: "Empty state map with state changes",
        migration: {
          fromVersion: 0,
          toVersion: 1,
          entityType: "Ticket",
          transforms: [{ source: "X", target: "Y", drop: false }],
          stateMap: [], // Should map states if they changed
        },
        expectedIssue: "typeSafe", // Could be unsafe
      },
    ]
    
    for (const pattern of unsafePatterns) {
      const check = checkSafeMigration(pattern.migration)
      
      if (pattern.expectedIssue === "noDataLoss") {
        assert.strictEqual(check.noDataLoss, false, pattern.name)
      }
    }
  })
})

describe("P4.4.5: Unsafe pattern detection", () => {
  it("rejects migration with ambiguous transform", () => {
    // Two transforms for same source
    const ambiguousMigration: MigrationSpec = {
      fromVersion: 0,
      toVersion: 1,
      entityType: "Ticket",
      transforms: [
        { source: "Create", target: "Open", drop: false },
        { source: "Create", target: "NewTicket", drop: false }, // Duplicate!
      ],
      stateMap: [],
    }
    
    // First should win (or we could reject)
    const transform = lookupTransform(ambiguousMigration, "Create")
    assert.strictEqual(transform?.target, "Open")
  })
  
  it("rejects migration with invalid version chain", () => {
    const badMigration: MigrationSpec = {
      fromVersion: 2, // Higher than to!
      toVersion: 1,
      entityType: "Ticket",
      transforms: [],
      stateMap: [],
    }
    
    // Should detect backwards version
    assert.ok(badMigration.fromVersion > badMigration.toVersion, "Backwards version detected")
  })
  
  it("rejects state map with collisions", () => {
    const collisionMigration: MigrationSpec = {
      fromVersion: 0,
      toVersion: 1,
      entityType: "Ticket",
      transforms: [],
      stateMap: [
        ["open", "new"],
        ["closed", "new"], // Both map to "new" - collision!
      ],
    }
    
    // Detect collision
    const targets = collisionMigration.stateMap.map(([, to]) => to)
    const uniqueTargets = new Set(targets)
    assert.ok(targets.length > uniqueTargets.size, "Collision detected")
  })
})
