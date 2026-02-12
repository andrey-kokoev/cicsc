# Pilot Unsupported Features (Explicit Rejections)

Requests requiring any item below must be rejected at compile/typecheck or deployment gate.

## Query/Constraint Surface

- Query joins outside currently supported lowering subset.
- Grouping semantics beyond tested aggregate surface.
- Non-supported bool_query assert expression forms.

## Runtime/Execution

- Runtime special-casing by vertical name or custom shadow-column branches.
- Silent fallback behavior when constraint/query lowering is unsupported.
- Best-effort migration execution without replay verification.

## Evolution

- Payload-transform migrations outside current verified migration class.
- Cross-type migration transforms.
- Migration cutovers without verification artifact.

## Infrastructure

- Multi-region causal/CRDT behavior claims.
- Production Postgres rollout as part of this pilot phase.

## Rejection Handling

- Return structured error with actionable path-qualified reason.
- Add forced missing primitive to roadmap as new checkbox.
