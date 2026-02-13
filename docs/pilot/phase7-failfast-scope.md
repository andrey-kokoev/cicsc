# Phase 7 Fail-Fast Out-of-Scope Gate

Report artifact:
- `docs/pilot/phase7-failfast-scope.json`

Required checks:
- backend scope contracts declare deferred operators explicitly
- negative typecheck/lowering suites reject unsupported constructs
- backend semantics policy stays explicit about scoped deltas

This artifact closes `P7.1.3` / `X1.3`.
