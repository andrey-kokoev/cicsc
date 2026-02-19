# CICSC — Constructively Invariant Control System Compiler

CICSC is a compiler + runtime substrate for constructing executable socio-technical control systems from formal specifications, with invariant-preserving evolution as a design constraint.

The repository contains:
- a user-facing Spec format,
- a Core IR with enforced semantics,
- backend lowering (SQLite/D1),
- a transactional runtime,
- and a SQLite execution ledger toward constructive migrations.

---

## What CICSC Is (Operationally)

CICSC implements the pipeline:

```
Spec (YAML/JSON)
  → compile
Core IR (typed, backend-agnostic)
  → typecheck
  → schema-gen
SQLite/D1 schema + lowering
  → install
Runtime (tx, invariants, views, verify)
```

The runtime executes:
- commands (append events),
- reducers (history → state),
- constraints (invariants),
- views (queries),
- verification (replay-checked).

State is reducible from event history.

---

## Invariants Enforced

- Transactional command execution  
  Writes occur inside BEGIN IMMEDIATE transactions.

- Deterministic replay  
  State is a fold over event history.

- Invariant enforcement  
  Snapshot and global constraints are checked before commit.

- Backend conformance  
  SQL lowering is tested against an oracle interpreter.

- Constructive invariance (planned)  
  Migrations must be total and replay-verified.

These properties are enforced by design and tests.

---

## What Exists Today (v0)

- Spec → Core IR compiler (v0; Spec is IR-shaped YAML)
- Core IR typechecker
- SQLite/D1 schema generator from IR (shadow columns)
- Transactional runtime (commands, views, verify)
- Oracle interpreter + SQL lowering conformance tests
- HTTP API:
  - `POST /compile`
  - `POST /install-from-spec` (optional patch)
  - `POST /cmd/:type/:name`
  - `GET /view/:name`
  - `GET /verify`
- Roadmap and working agreement
- Category model of the substrate

---

## What Does Not Exist Yet

- Spec DSL sugar (Spec remains IR-shaped)
- Bundle registry (R2/KV)
- Tenant → bundle binding
- Migrations / versioned evolution
- Postgres adapter
- Index generation from views/constraints
- Per-type snapshot tables

These items are tracked in the execution ledger.

---

## How to Run a Minimal System (v0)

1) Compile Spec:
```
POST /compile
```

2) Install schema + bind tenant:
```
POST /install-from-spec?tenant_id=t1
```

3) Issue a command:
```
POST /cmd/Ticket/create
```

4) Query a view:
```
GET /view/tickets_by_lane?tenant_id=t1
```

5) Verify invariants:
```
GET /verify?tenant_id=t1
```

## CLI

Use the lightweight CLI wrapper:

```bash
node cli/cicsc.mjs compile --spec ./spec.json --server http://localhost
node cli/cicsc.mjs install --spec ./spec.json --tenant t1 --server http://localhost
node cli/cicsc.mjs verify --tenant t1 --server http://localhost
node cli/cicsc.mjs gates --suite required
node cli/cicsc.mjs migration-preflight --from ./bundle.v0.json --to ./bundle.v1.json --events ./events.v0.json --migration v0_to_v1
node cli/cicsc.mjs migration-dry-run --from ./bundle.v0.json --to ./bundle.v1.json --events ./events.v0.json --migration v0_to_v1 --artifact ./artifacts/migration-dry-run.json
node cli/cicsc.mjs migration-rollback --to ./bundle.v1.json --events ./events.v1.json --migration v0_to_v1 --out-events ./events.v0.rolledback.json
```

## Local Dev Harness

Run the worker locally against a file-backed SQLite DB:

```bash
CICSC_DB_PATH=./cicsc.dev.sqlite node runtime/dev/harness.mjs
```

---

## Normative Design Documents

- `docs/foundations/category-model.md`  
  Categorical model of CICSC.

- `ROADMAP_WORKING_AGREEMENT.md`  
  Roadmap execution rules.

- `AGENTS.md`  
  Contributor and agent guidelines.

- `docs/spec/non-programmer-workflows.md`
  Workflow-authoring guide for non-programmer operators.

- `JOURNEY_VECTOR.md`
  Canonical objective-to-status-to-evidence navigation document.

These documents constrain implementation choices.

---

## Roadmap

The canonical execution plan/status ledger is:

- `state/ledger.db`


---

## Design Constraints

- No bundle-specific logic in runtime.
- No backend-only semantics.
- No partial migrations.
- No in-place mutation of history.
- Compile-time rejection where possible.
- Conformance tests for lowering changes.

---

## Status

The system implements a working substrate with transactional semantics and invariant enforcement. Further work is required for bundle persistence, migrations, and additional backends.

Lean kernel status:
- Lean Kernel v1 acceptance: complete.
- Lean Kernel v1.5 coherency closure: complete (canonical constraint semantics, `checkIR -> WFIR`, declarative typing soundness bridge, replay WF closure).

---

## License

Apache 2.0 License. See LICENSE file for details.
