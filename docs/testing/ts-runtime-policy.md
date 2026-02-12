# TypeScript Test Runtime Policy

To avoid ad hoc test execution variance, all Node-based `.ts` tests must run through:

- `./scripts/node_test.sh`

This wrapper enforces a fixed module-resolution strategy:

- Node test runner (`--test`)
- explicit custom loader (`tests/harness/ts-extension-loader.mjs`)

Automation entrypoints (`scripts/phase3_ci_target.sh`, `scripts/ci.sh`) must use this wrapper, not inline `node --loader ...` calls.
