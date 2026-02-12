# How To Build a Vertical in CICSC

## 1. Define Domain Boundary

- Choose one bounded workflow (e.g., Ticketing, CRM pipeline, Kanban flow).
- Identify entity types, states, command intents, and invariants.

## 2. Author Spec DSL

- Declare `entities`, `commands`, `reducers`, `views`, and `constraints`.
- Keep guards explicit and deterministic.

## 3. Compile + Typecheck

- Run compile path and fix all Spec/IR type errors.
- Reject unsupported lowering patterns early.

## 4. Validate Runtime Semantics

- Execute command paths transactionally.
- Verify replay determinism and constraint enforcement.

## 5. Add Conformance Tests

- Add oracle tests for business logic.
- Add SQL-vs-oracle tests for lowered queries/constraints.

## 6. Prepare Evolution

- Define migration edges and total transforms.
- Verify replay before any cutover.

## 7. Operate

- Bind tenants to bundle/version.
- Monitor verify reports and invariant drift.
