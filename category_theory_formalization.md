# Categorical Semantics of Control Plane Integration

## 1. The Category of States

### Definition 1.1: The Category **State**

Objects are tuples `(G, A, R)` where:
- `G ∈ Git` is a git object graph
- `A ⊆ Checkbox × (Agent ∪ {⊥})` is assignment partial function
- `R ⊆ Worktree × Checkbox` is claim relation

Morphisms `σ: (G₁, A₁, R₁) → (G₂, A₂, R₂)` are valid transitions.

### Definition 1.2: The Subcategory **Valid**

**Valid** ↪ **State** is the full subcategory where:
1. ∀c ∈ dom(A): A(c) = ⊥ ∨ work_exists(c, G)  [Claimed work exists]
2. ∀(w,c) ∈ R: branch(w) descends_from(main)  [FF property]
3. ∀c ∈ Checkbox: at_most_one(A(c))  [No double assignment]

The inclusion functor `ι: Valid ↪ State` is faithful but not full.

---

## 2. The Integration Functor

### Definition 2.1: Evidence Functor `E: State → Set`

Maps each state to its evidence set:
```
E(G, A, R) = { commits(g) | g ∈ G, message_matches(complete_pattern) }
```

### Definition 2.2: The Synchronization Problem

Given `S ∈ State`, find `V ∈ Valid` and `e: S → ι(V)` such that:
- `E(e)` is isomorphism (evidence preserved)
- `e` is universal (initial among such)

**Theorem 2.1:** No such left adjoint `L: State → Valid` exists.

*Proof:* Some states are irreparable (e.g., semantic mismatch). The counit would not exist. ∎

---

## 3. Fast-Forward as Categorical Property

### Definition 3.1: The Slice Category **State/main**

Objects are morphisms `f: main → S` (worktrees branched from main).

### Definition 3.2: FF Morphism

A morphism `f: S₁ → S₂` is **FF** if:
```
∃! g: main → S₂ such that f ∘ (main → S₁) = g
```
in other words, the triangle commutes uniquely.

### Definition 3.3: The Subcategory **FF-State**

Objects: `(G, A, R)` where all worktrees satisfy FF property.
Morphisms: Only FF morphisms.

**Proposition 3.1:** **FF-State** is a preorder (at most one morphism between objects).

*Proof:* FF property + git's content addressing = uniqueness. ∎

---

## 4. Integration as Coequalizer

### Definition 4.1: Parallel Transitions

Two workers create parallel morphisms:
```
main ──w₁──► W₁
main ──w₂──► W₂
```

### Definition 4.2: Integration Attempt

The integration is a pushout:
```
        w₁
main ──────► W₁
 │            │
 │w₂          │ι₁
 ▼            ▼
W₂ ────► W₁ ∪main W₂
        ι₂
```

**Theorem 4.1:** The pushout exists in **State** iff `w₁` and `w₂` are independent.

**Corollary 4.1:** In **FF-State**, pushout exists iff `W₁` and `W₂` are comparable (one descends from the other).

*This is exactly the FF-only merge constraint.*

---

## 5. The Recency Check as Terminal Object

### Definition 5.1: Recency Category **Recent(t)**

Objects: States where `age(worktree) ≤ t`
Morphisms: FF morphisms preserving recency

**Proposition 5.1:** `main` is terminal in **Recent(t)**.

*Proof:* Any recent worktree has unique FF morphism to main (the merge). ∎

**Theorem 5.2 (Recency implies FF):** 
If all work is integrated within window `t`, then **Recent(t)** is equivalent to **FF-State**.

*Proof:* By recency, main hasn't advanced past merge-base, so FF always possible. ∎

---

## 6. Structural vs Semantic Invalidity

### Definition 6.1: Structural Functor `S: State → Structure`

Maps to underlying graph structure (forgetting content).

### Definition 6.2: Semantic Functor `M: State → Meaning`

Maps to "intended work" (checkbox semantics).

### Theorem 6.1 (Separation of Concerns):

The FF-only design makes `S⁻¹(valid)` reachable states all valid.

But `M⁻¹(valid)` remains non-empty for some invalid states (false confirmation).

**Proof:** 
- Structural: Git's content addressing makes FF merges deterministic.
- Semantic: No computable functor verifies semantic equivalence (halting problem). ∎

---

## 7. The Integration Monad

### Definition 7.1: The Maybe Monad on **State**

`T(S) = S + {⊥}` representing "success or rejection".

### Definition 7.2: Integration as Kleisli Arrow

```
integrate: Hom(State, State) → Hom(State, T(State))
integrate(f) = if valid(f) then η ∘ f else ⊥
```

**Theorem 7.1:** `integrate` is a natural transformation from `Id` to `T` on **Valid**.

*Proof:* On valid states, `valid(f)` always true, so `integrate(f) = η ∘ f`. ∎

---

## 8. Concurrency as Product

### Definition 8.1: Concurrent Claims

Two agents claim simultaneously:
```
claim₁, claim₂: main → main' 
```

### Theorem 8.1: **Valid** has no products for concurrent claims.

*Proof:* Would require both assignments active, violating at_most_one. ∎

### Theorem 8.2: **FF-State** has products given by serialization.

*Proof:* First claim creates `main₁`, second is based on `main₁`, giving ordered product. ∎

**This is the "first wins" semantics.**

---

## 9. Summary: The FF-Only Axiom

The system satisfies:

```
Axiom (FF-Only): ∀ f: main → W, ∃! g: W → main such that g ∘ f = id_main
                 ⇒ g is FF-merge
```

**Categorical Consequences:**
1. **State/main** is a preorder (Proposition 3.1)
2. Pushouts exist iff comparable (Corollary 4.1)
3. `main` is terminal in recency windows (Proposition 5.1)
4. Products serialize to first-wins (Theorem 8.2)

**Trade-off:** The category is not complete (missing coproducts for conflicts), but the remaining invalid states are only semantic, not structural.

---

## 10. The Invariant Preservation Theorem

**Theorem 10.1:** In **FF-State** with recency constraint `t`, all reachable invalid states are in the kernel of `S` (semantic only).

*Proof sketch:*
1. Structural validity: FF + recency → no merge conflicts
2. No locks needed: Git push atomicity = morphism uniqueness
3. No partial updates: Commits are atomic in **State**
4. Semantic errors: Not detectable by `S`, hence in ker(S). ∎
