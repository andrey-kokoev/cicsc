# CICSC Isolation Guarantees

> Phase 4: Concurrency + Transaction Reliability (P4.3.5)  
> Document ID: cicsc/spec/isolation-guarantees-v1  
> Status: Formalized with explicit limits

---

## 1. Supported Isolation Guarantees

### 1.1 Snapshot Isolation (SI)

**Definition**: Each transaction reads from a consistent snapshot of the database as of the time the transaction started.

**Formal Property**:
```lean
def snapshotAt (h : History) (ts : Nat) (sid : StreamId) : State :=
  -- State includes all events with timestamp ≤ ts in the stream
```

**Guarantees Provided**:

| Property | Guarantee | Formal Basis |
|----------|-----------|--------------|
| No Dirty Reads | ✓ Guaranteed | `snapshotAt` excludes uncommitted events |
| Non-Repeatable Reads | ✓ Prevented | Snapshot doesn't change mid-transaction |
| Phantom Reads | ✓ Prevented | For snapshot-based queries |
| Write-Write Conflicts | ✓ Detected | Abort or serialize |

### 1.2 Read Committed (RC)

**Definition**: Transactions see only committed data, but may see different values on re-read.

**Use Case**: Long-running read transactions where SI would cause too much version churn.

---

## 2. Formal Properties

### 2.1 Dirty Read Exclusion

```lean
theorem noDirtyReads
  (tx : Transaction)
  (h : History)
  (tsStart : Nat) :
  ∀ e ∈ tx.readSet,
    e.ts ≤ tsStart →
    e.committed :=
  -- Proof: snapshotAt only includes events with ts ≤ tsStart
  -- Uncommitted events have ts > transaction start
```

### 2.2 Non-Repeatable Read Exclusion

```lean
theorem snapshotConsistent
  (tx : Transaction)
  (snapshotTs : Nat) :
  ∀ query executed during tx,
    query sees same snapshot at snapshotTs :=
  -- Proof: snapshotTs fixed at transaction start
```

### 2.3 Write-Write Conflict Detection

```lean
theorem writeWriteConflictDetected
  (tx1 tx2 : Transaction)
  (s : StreamId) :
  tx1.writes s ∧ tx2.writes s ∧ concurrent tx1 tx2 →
  tx1.aborted ∨ tx2.aborted ∨ serialized tx1 tx2 :=
  -- Proof: Lock manager or timestamp ordering
```

---

## 3. Explicitly Excluded Scenarios

The following are **NOT** guaranteed by CICSC Phase 4:

### 3.1 Write Skew

**Scenario**: Two transactions read overlapping data sets and write to disjoint sets.

```
T1: read A, read B, write A
T2: read A, read B, write B
-- Both can commit under SI, violating serializability
```

**Mitigation**: Application-level constraints or explicit locking.

### 3.2 Lost Updates

**Scenario**: Two transactions read same data, one updates, second overwrites.

```
T1: read x=10, write x=15
T2: read x=10, write x=20 (overwrites T1)
-- Result: x=20, T1's update lost
```

**Mitigation**: Optimistic locking with version checks.

### 3.3 Full Serializability

**Excluded**: Serializable snapshot isolation (SSI) with predicate locking.

**Reason**: Complexity vs. benefit trade-off for current target workloads.

---

## 4. Transaction Model

### 4.1 Multi-Stream Transactions

```
Transaction {
  id: string
  commands: List<{
    stream: StreamId
    eventType: string
    payload: Value
  }>
}
```

**Atomicity**: All events in a transaction commit together or all abort.

### 4.2 Execution Semantics

```
execTransaction(tx, history) =
  1. Acquire locks on all target streams
  2. If any lock fails → ABORT (write-write conflict)
  3. Evaluate guards for all commands
  4. If any guard fails → ABORT
  5. Generate events with sequential seq per stream
  6. Append all events atomically → COMMIT
  7. Release locks
```

### 4.3 ACID Properties

| Property | Level | Implementation |
|----------|-------|----------------|
| Atomicity | Full | All-or-nothing event append |
| Consistency | Per-stream | Seq ordering, state transitions |
| Isolation | Snapshot | Timestamp-based snapshots |
| Durability | Best-effort | See storage limitations |

---

## 5. Concurrency Primitives

### 5.1 Happens-Before Relation

```lean
def happensBefore (e1 e2 : Event) : Prop :=
  sameStream e1 e2 ∧ e1.seq < e2.seq
```

**Properties**:
- Irreflexive: `¬happensBefore e e`
- Transitive: `happensBefore e1 e2 → happensBefore e2 e3 → happensBefore e1 e3`
- Asymmetric: `happensBefore e1 e2 → ¬happensBefore e2 e1`

### 5.2 Concurrent Events

```lean
def concurrent (e1 e2 : Event) : Prop :=
  sameStream e1 e2 ∧ ¬happensBefore e1 e2 ∧ ¬happensBefore e2 e1
```

**Property**: Concurrent events commute under `CommutesOnConcurrent` reducer property.

### 5.3 Causally Equivalent Histories

```lean
inductive CausallyEquivalent : History → History → Prop
  | refl: CausallyEquivalent h h
  | swap: concurrent e1 e2 → 
          CausallyEquivalent (pre ++ e1::e2::post) (pre ++ e2::e1::post)
  | trans: CausallyEquivalent h1 h2 → CausallyEquivalent h2 h3 → 
           CausallyEquivalent h1 h3
```

**Theorem**: `CausallyEquivalent h1 h2 → replay h1 = replay h2` (given `CommutesOnConcurrent`).

---

## 6. Implementation Notes

### 6.1 SQLite Backend

- Uses `BEGIN IMMEDIATE` for write transactions
- Snapshot isolation via WAL mode
- Row-level conflict detection via `version` column

### 6.2 Postgres Backend

- Uses `REPEATABLE READ` isolation level
- Serialization failures retried at application level
- Advisory locks for stream-level granularity

### 6.3 Limitations

| Limitation | Impact | Mitigation |
|------------|--------|------------|
| No distributed consensus | Single-node only | Application-level sharding |
| No online schema change | Migration requires brief pause | Scheduled maintenance windows |
| Best-effort durability | Crash may lose in-flight tx | Write-ahead logging |

---

## 7. Verification Checklist

- [x] Happens-before relation formalized
- [x] Concurrent events defined
- [x] Causal equivalence established
- [x] Replay determinism proved
- [x] Write-write conflict detection implemented
- [x] Snapshot isolation documented
- [ ] Serializable isolation (deferred)
- [ ] Distributed consensus (deferred)

---

## 8. References

1. **Lean Concurrency**: `lean/Cicsc/Core/Semantics/Concurrency.lean`
2. **Causality Replay**: `lean/Cicsc/Core/Semantics/CausalityReplay.lean`
3. **Transaction Tests**: `tests/concurrency/transaction-model.test.ts`
4. **Causality Tests**: `tests/concurrency/causality-replay.test.ts`
