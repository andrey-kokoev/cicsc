# /docs/spec/proofs.md

# Proof Obligations and Verification Procedures (Normative)

## 0. Status

This document defines proof obligations and verification procedures required for CICSC v0 conformance.

This document is normative.

---

## 1. Objects

Let:

- `Spec_n` be Spec at version n
- `IR_n` be Core IR compiled from `Spec_n`
- `H_n` be the event history at version n
- `Reduce(IR, H)` be deterministic reduction producing snapshots and derived state
- `Mig_{n→n+1}` be the migration transform mapping `H_n → H_{n+1}`
- `F_n` be the set of declared functional properties at version n (guards, constraints, SLAs, auth)
- `T_n` be transformability predicate at version n

---

## 2. Proof Obligation: Reducer Determinism

For any `IR_n` and any history `H_n`:

`Reduce(IR_n, H_n)` MUST be deterministic.

Procedure:
- compile IR
- replay history twice
- assert snapshot equality byte-for-byte under canonical serialization

---

## 3. Proof Obligation: Migration Totality

For any migration `Mig_{n→n+1}`:

`Mig_{n→n+1}` MUST be total over all events in `H_n`.

Procedure:
- define transform over event domain: every event maps to:
  - a new event, or
  - a drop marker explicitly allowed
- run transform over full history
- assert no “undefined” or runtime exceptions occur

---

## 4. Proof Obligation: History Preservation

For any admissible upgrade:

`H_{n+1} = Mig_{n→n+1}(H_n)`

and post-upgrade state is reducible from migrated history:

`State_{n+1} = Reduce(IR_{n+1}, H_{n+1})`

Procedure:
- materialize migrated event storage
- rebuild snapshots strictly by replay
- forbid direct snapshot mutation

---

## 5. Proof Obligation: Functional Preservation

All functional properties in `F_n` MUST hold after upgrade on migrated history:

For guards/constraints (state predicates):

`∀h ∈ H_n: F_n(Reduce(IR_{n+1}, Mig(h))) = true`

For SLAs:
- computed deadlines and breach status MUST be preserved under event semantics or explicitly redefined as ΔF with corresponding migration.

Procedure:
- after rebuilding, evaluate:
  - all bool_query constraints against snapshots
  - all snapshot constraints in VM
  - SLA status computed from replay vs stored projection
- reject if any violation occurs

---

## 6. Proof Obligation: Transformability Preservation

Transformability is defined as existence of future migrations:

`T(s) := ∃Spec', Mig' total such that Spec' typechecks and Mig' total over H(s)`

CICSC v0 requires the weaker operational obligation:

- the system remains within Core IR expressiveness after upgrade
- migrations remain representable and executable

Procedure:
- validate `IR_{n+1}` against Core IR schema
- validate adapter can lower `IR_{n+1}` under declared capabilities
- reject upgrades that introduce unsupported constructs

---

## 7. Proof Obligation: Adapter Semantic Fidelity

For any adapter A and IR:

- adapter query execution MUST match Query AST semantics
- adapter constraint evaluation MUST match BoolQueryConstraint semantics

Procedure:
- run conformance test suite:
  - generate random histories and snapshots
  - compare adapter-evaluated queries vs reference interpreter for Query AST
  - compare adapter-evaluated constraints vs reference evaluation

---

## 8. Replay Verification Report

Replay verification MUST produce a report containing:

- Spec versions (from/to)
- Core IR hash (from/to)
- migration hash
- adapter identity + capabilities
- counts of events transformed
- snapshot rebuild summary
- constraint evaluation summary
- SLA evaluation summary
- pass/fail result
- timestamp

Cutover MUST be forbidden unless report is pass.

---

## 9. Undefined Behavior

If any proof obligation fails:

- the upgrade is non-admissible
- cutover MUST NOT occur
- system remains at version n
