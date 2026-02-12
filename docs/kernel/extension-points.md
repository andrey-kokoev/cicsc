# Kernel Extension Points

## 1. Intrinsics

- Provide custom `VmIntrinsics` implementation for auth/policy/domain functions.
- Must preserve determinism for replay-critical paths.

## 2. Storage Backends

- Implement event storage compatible with kernel event model.
- Ensure stream ordering and immutability guarantees.

## 3. Constraint Execution

- Additional constraint forms can be added at compile/lowering layers.
- Kernel constraint semantics must remain oracle-equivalent.

## 4. Migration Strategies

- Custom transform planners may wrap `transformHistoryWithMigration`.
- Must preserve totality and replay-verification gate.

## 5. Reporting/Audit

- Integrate custom verify/audit sinks using kernel verification outputs.
