# Kernel API Stability Guarantees

## Scope

Stable kernel surface is defined by exports in `kernel/src/index.ts`.

## Guarantees

1. Patch releases: no breaking changes to stable exports.
2. Minor releases: additive exports only.
3. Major releases: breaking changes allowed with migration notes.

## Deprecation

- Deprecated exports must remain for at least one minor release cycle.
- Removals require changelog entry and replacement guidance.

## Behavioral Stability

- Replay and verification semantics for unchanged IR versions are stable.
- Deterministic behavior changes require explicit major-version announcement.
