# Phase 30 Objective Closure Scenario Contract

Artifacts:
- `docs/pilot/phase30-objective-closure-scenario.json`

This contract freezes the single end-to-end adversarial scenario used to decide
project objective closure in Phase 30.

Frozen pipeline:
1. Spec compile
2. IR typecheck
3. SQLite execution-vs-oracle differential
4. Postgres execution-vs-oracle differential
5. Migration cutover + replay verification

Blocking policy:
- If any objective verdict is `not_met`, completion claim is blocked and only forced-next
  execution-ledger checkboxes may be added.
- If all objective verdicts are `met`, objective completion claim is allowed.
