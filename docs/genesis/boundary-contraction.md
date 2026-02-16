# Boundary Contraction in Control Plane Integration

## The Pattern

Rather than distribute constraints across all operations, we concentrate them at a single boundary.

## Categorical Structure

- **Inside boundary**: Workers operate in `State/main` (unconstrained)
- **Boundary**: `integrate : W → main` 
- **Constraint**: FF-morphism required

## Why This Works

The category **FF-State/main** is a preorder:
- At most one morphism between objects
- No decision points, no race conditions
- Invalid states literally don't exist as morphisms

## Trade-off

We lose:
- Concurrent integration (serialized by first-wins)
- Long-lived branches (recency constraint)

We gain:
- Invalid structural states are **unreachable**
- No locks, no coordination complexity
- The category itself enforces correctness

## Relation to Type Systems

This is the collaboration analog of:
- Type checking at function boundaries
- Monadic effects with `run` as the boundary
- Capability-based security with explicit gates

## The Three Layers

| Layer | Artifact | Trust Level |
|-------|----------|-------------|
| 1 | `lean/Cicsc/Evolution/FFIntegration.lean` | Highest (machine-checked) |
| 2 | `docs/foundations/category-model.md §11` | Contract (normative) |
| 3 | `control-plane/integrate.sh` | Executable trace |

## Implementation

The categorical constraint `IsFFMorph` is implemented as:
```bash
git merge --ff-only work/${AGENT}/${CHECKBOX}
```

When this succeeds, we have a proof-carrying morphism in **FF-State/main**.
When it fails, no morphism exists—the state is unreachable.

## The Axiomatic Bridge

We trust git's `--ff-only` as the ground truth for the FF-property:

```lean
axiom git_ff_implies_descent : 
  ∀ (main worktree : Commit) (g : GitGraph),
    git_merge_ff_succeeds main worktree → IsFFMorph main worktree g
```

**Proof obligation**: Prove this equivalence formally to move from Option 1 (axiomatic) to Option 2 (refinement).

## Historical Context

This design emerged from analyzing collaboration friction:

- Distributed constraints caused race conditions
- Rebase operations broke structural invariants  
- Merge conflicts created invalid states

The insight: **constrain only the boundary**, not the interior.
