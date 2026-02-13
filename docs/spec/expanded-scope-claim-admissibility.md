# Expanded-Scope Claim Admissibility Policy

This policy defines the formalization requirements that must be met before a claim (concurrency, operator usage, migration pattern) is admissible as a "proven" semantic claim in Era 2.

## Admissibility Matrix

| Claim Class | Expanded Feature | Required Formalization Artifact | Admissibility Status |
|-------------|------------------|---------------------------------|----------------------|
| **Concurrency** | Adversarial Replay | `soundness_of_conflict_matrix` in `Semantics/Replay.lean` | **Blocked** |
| **Governance** | Drift-Budget | `WFGovernance` predicate in `Semantics/Commands.lean` | **Blocked** |
| **DSL** | Desugaring | `spec_to_ir_well_typed` proof in `Meta/Typecheck.lean` | **Blocked** |
| **Migration** | Joined Migrations | `replay_commutes` for join sources in `Evolution/Migration.lean` | **Blocked** |
| **Operators** | `HAVING`, `EXISTS` | `HavingSemantics`, `ExistsSemantics` in `Cicsc/Core/Syntax.lean` | **Blocked** |

## Rule of Admissibility

1. Any checkbox or artifact claiming "proven" status for an expanded feature must be gated by the corresponding formalization artifact.
2. If the formalization artifact is missing or incomplete, the claim is treated as **Experimental** and cannot pass the Phase 33 block gate.
3. Admissibility is binary: either the proof/semantics exists in the Lean kernel and is replay-verified, or the feature is restricted in the backend lowerer.

## Enforcement Mechanism

- The `./scripts/phase33_ax22_formalization_gate.sh` script verifies the presence and status of these artifacts in the `lean/` workspace.
