# Stress Test Results: Fast-Forward-Only Integration

## Structural Invalid States (Now Unreachable)

| Path | Scenario | Prevention |
|------|----------|------------|
| 1 Lock Race | Simultaneous integration | Git push atomicity |
| 2 Zombie Lock | Crash mid-operation | No locks used |
| 3 Partial Integration | Half-updated state | Single atomic commit |
| 6 Concurrent Claim | Double assignment | First-wins semantics |

**Verdict:** ✅ All unreachable via FF-only design

---

## Remaining Reachable Invalid States

### Path 5: False Confirmation
**Scenario:** Worker commits "complete: BX1.1" but actually implemented BX1.2

**Why reachable:** Git only verifies commit message syntax, not semantic truth

**Mitigation options:**
1. Content-addressed verification (hash of work vs expected)
2. Human review gate
3. Automated test verification (tests pass = claim valid)

**Current verdict:** ❌ Reachable

---

### Path 7: Orphaned Branch → Rebase Corruption
**Scenario:** 
- Worker branches from main@T0
- Main advances significantly
- FF merge fails
- Rebase conflicts
- Worker resolves incorrectly

**Why reachable:** Rebase requires human judgment for conflicts

**Mitigation options:**
1. Rebase prohibition (reject if not FF, force redo)
2. Time-bounded integration window
3. Automated conflict resolution (impossible in general)

**Current verdict:** ❌ Reachable

---

### Path 8: Untracked Integration
**Scenario:** Worker integrates commit without checkbox reference

**Why reachable:** No enforcement of commit message format during merge

**Mitigation:**
1. Commit message linting in integrate.sh
2. Reject commits not matching "complete: CHECKBOX"

**Current verdict:** ❌ Reachable

---

### Path 9: Network Partition → Retry Conflict
**Scenario:**
- Local FF merge succeeds
- Push fails (timeout)
- Retry: main moved
- Rebase required

**Same as Path 7:** Rebase corruption risk

**Current verdict:** ❌ Reachable

---

## The Fundamental Tension

```
FF-Only Design          Reality
─────────────────       ─────────────────
No locks needed    ←→   Conflicts happen
Atomic operations  ←→   Network partitions
No rebase needed   ←→   Concurrent work
Unreachable states ←→   Humans resolve conflicts
```

**The choice:**
1. **Accept rebase risk:** Build strong verification (tests, review)
2. **Reject rebase:** Throw away work to preserve invariants

---

## Recommended Hardening

To make remaining paths unreachable:

```bash
# integrate.sh hardened

# 1. Commit message enforcement (Path 8)
git log --format=%s HEAD^..HEAD | grep -E "^complete: [A-Z]+[0-9]+\.[0-9]+$" || exit 1

# 2. Recency check (Path 7, 9)
BRANCH_BASE=$(git merge-base HEAD origin/main)
MAIN_TIP=$(git rev-parse origin/main)
if [ "$BRANCH_BASE" != "$MAIN_TIP" ]; then
    echo "ERROR: Branch too old. Abandon and redo work."
    exit 1
fi

# 3. Pre-merge validation (Path 4)
./control-plane/check_gates.sh || exit 1

# 4. FF-only merge
git merge --ff-only "$WORKER_BRANCH" || exit 1

# 5. Push (atomic)
git push origin main
```

**Result:** If any check fails, integration aborts. No manual resolution allowed.

---

## Trade-off Summary

| Approach | Invalid States | Lost Work | Complexity |
|----------|---------------|-----------|------------|
| v1 (59 scripts) | Prevented (mostly) | Low | Very High |
| v2 simple (6 scripts) | Reachable | Medium | Low |
| FF-only + recency | Unreachable | High (rejected work) | Medium |
| FF-only + rebase | Reachable (conflict resolution) | Low | Medium |

**Recommendation:** FF-only + recency check for invariant-critical paths; accept rebase risk for velocity paths.
