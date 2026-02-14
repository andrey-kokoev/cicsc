# AGENTS.md

This file defines how an execution agent should work on the CICSC repository.
It is not user-facing documentation. It is operational guidance for contributors
and autonomous agents executing the execution plan.

---

## Mission

Turn CICSC from a working substrate prototype into:

> A correct, invariant-preserving compiler + runtime for socio-technical systems,
> with a real user intent DSL and migration guarantees.

Primary success criteria:

- Invariants hold under concurrency.
- IR and runtime semantics are aligned and enforced by typechecking + conformance tests.
- Spec DSL is usable by humans.
- Migrations are executable and replay-verified.
- Backends (SQLite/D1, Postgres) are semantically equivalent to the oracle.

Lean proof baseline:
- Lean Kernel v1.5 is the coherency-complete baseline for kernel semantics.
- New semantics work must preserve the canonical evaluator/typing/WF bridges established in v1.5.

## Main Agent Day-0 Checklist

If you are the main agent opening this repository for the first time, do this in order:

1. `./control-plane/scripts/generate_views.sh`
2. `./control-plane/scripts/collab_help.sh --role main --worktree /home/andrey/src/cicsc`
3. `./control-plane/scripts/collab_inbox.sh --worktree /home/andrey/src/cicsc --refresh`
4. `./scripts/check_canonical_execution_model.sh`
5. Dispatch or delegate only through WMCC command surface (`collab_dispatch.sh`, `collab_delegate_worktree.sh`).

Do not create local ad hoc task files. Protocol truth is mailbox + append-only message events.

## Deterministic Invocation Contract

If the instruction is only:

`Follow AGENTS.md`

then execute exactly this protocol:

1. `cd /home/andrey/src/cicsc`
2. `./control-plane/scripts/generate_views.sh`
3. Resolve your worktree path:
   - main agent: `WORKTREE=/home/andrey/src/cicsc`
   - worker agent: `WORKTREE=<your assigned worktree>`
4. Sync your worktree to current `main` before reading inbox:
   - `git -C "$WORKTREE" fetch origin`
   - `git -C "$WORKTREE" rebase origin/main`
   - if rebase cannot proceed, stop and report blocker (do not continue on stale scripts/protocol)
5. Read actionable inbox:
   - `./control-plane/scripts/collab_inbox.sh --worktree "$WORKTREE" --refresh`
6. If no actionable messages: stand down and report `no actionable inbox messages`.
7. If actionable messages exist: process mailbox protocol (claim -> fulfill with required evidence -> commit), repeating until no actionable messages remain.
8. Return a completion report containing:
   - `message_ref`
   - `assignment_ref`
   - `checkbox_ref`
   - `commit_sha`
   - `current_status`

### Intent Resolution Rule (Mandatory)

Interpret short operator instructions as follows:

- `status`
  - read-only mode
  - inspect and report mailbox/state
  - do not mutate collaboration state

- `process messages`
  - execution mode
  - process lifecycle transitions end-to-end (claim/fulfill for workers; ingest/close for main)
  - main full-cycle may include friction triage when enabled
  - continue until no actionable messages remain for the targeted worktree
  - do not pause for confirmation between deterministic protocol steps
  - preferred command:
    - main: `./control-plane/scripts/collab_process_messages.sh --role main --agent-ref <AGENT_...>`
      - full-cycle: `./control-plane/scripts/collab_process_messages.sh --role main --agent-ref <AGENT_...> --with-friction-triage --friction-decision accept_later`
    - worker: `./control-plane/scripts/collab_process_messages.sh --role worker --worktree "$WORKTREE"`
      - optional overrides: `--with <script> --auto-report --lazy`

## Normative Conceptual Sources

Execution guidance in this file is operational. Conceptual semantic intent is
normatively defined by `docs/genesis/*`.

Primary references:
- `docs/genesis/README.md`
- `docs/genesis/on-constructively-invariant-systems.md`
- `docs/genesis/constructively-invariant-control-system-compiler.md`
- `docs/genesis/constructive-invariance-evolution-control-plane.md`
- `docs/genesis/worktree-mediated-constructive-collaboration.md`
- `docs/genesis/constructive-accretion-method.md`

Precedence rule:
- if there is tension between execution convenience and genesis semantics,
  preserve genesis semantics and adjust process artifacts.

## Prose-to-Mechanism Boundary

`docs/genesis/*` is human-language semantic intent.
It is intentionally prose-first and not treated as machine-enforced status data.

Execution agents must use this boundary:
- ingest conceptual intent from `docs/genesis/*`,
- translate that intent into structured control-plane artifacts (`control-plane/*`),
- enforce behavior through scripts/gates over structured artifacts only.

Do not treat prose files as canonical status ledgers or gate inputs.

---

## Working Style

### -1. First Actions In Any Worktree (Mandatory)
Before doing any implementation work:

1. Run `./control-plane/scripts/generate_views.sh`
2. Sync worktree branch tip to `origin/main`:
   - `git -C "$WORKTREE" fetch origin`
   - `git -C "$WORKTREE" rebase origin/main`
3. Read inbox from `control-plane/views/worktree-mailboxes.generated.json` for
   the current worktree path
4. Process only actionable messages (`current_status` in `queued`, `sent`)

If no actionable inbox messages exist, do not invent local task authority.

WIP ordering rule:
- if any inbox message is `acknowledged` for your worktree, fulfill it before
  claiming additional `sent`/`queued` messages.
- `sent`/`queued` are claimable; `acknowledged` is already owned and should be
  executed to `fulfilled` before taking new ownership.

### 0. Canonical Execution Model (Mandatory)
Execution status truth is single-source:
- `control-plane/execution/execution-ledger.yaml` is the only canonical status ledger.
- `PHASE*.md` files are derived views; they are not authoritative for status.
- Planning/navigation docs (for example `PHASE_LEVEL_ROADMAP.md`, `JOURNEY_VECTOR.md`)
  must not contain execution status checkboxes.

Work unit policy:
- one checkbox = one commit,
- commit message must include the checkbox ID token (for example: `phase12 ac3.2`).

Before marking a checkbox complete, run:
- `./scripts/check_canonical_execution_model.sh`

This gate enforces:
- execution-ledger structural integrity,
- phase-view sync with execution-ledger,
- commit-evidence presence for checked checkboxes.

### 0.1 Canonical Collaboration Entry Point (Mandatory)
Worktree agents must use mailbox-driven execution:
- single entry point: `control-plane/views/worktree-mailboxes.generated.json`
- read inbox messages for the current worktree
- process actionable messages (`queued`/`sent`) in order
- append immutable `message_events` for lifecycle transitions and evidence

Protocol rule:
- `WORKTREE_ASSIGNMENT.md` is not allowed as an execution protocol artifact
- mailbox messages are the only admissible worktree task input

Message I/O command surface:
- execution location rule:
  - run all `control-plane/scripts/collab_*.sh` commands from repository root `/home/andrey/src/cicsc`
  - target worker context via `--worktree <path>`; do not invoke collab scripts from worker worktree directories
- required variables for examples below:
  - `ROOT=/home/andrey/src/cicsc`
  - `WORKTREE=<target worktree path>`
- operator quickstart (copy/paste):
  - `cd /home/andrey/src/cicsc`
  - `WORKTREE=/home/andrey/src/cicsc/worktrees/kimi`
  - `./control-plane/scripts/collab_inbox.sh --worktree "$WORKTREE" --refresh`
  - `./control-plane/scripts/collab_claim_next.sh --worktree "$WORKTREE" --commit`
- collaboration preflight gate:
  - `./control-plane/scripts/collab_validate.sh`
- quickstart command map (worker/main):
  - `./control-plane/scripts/collab_help.sh --role worker --worktree "$WORKTREE"`
- read inbox (actionable only):
  - `./control-plane/scripts/collab_inbox.sh --worktree "$WORKTREE" --refresh`
  - full history: `./control-plane/scripts/collab_inbox.sh --worktree "$WORKTREE" --refresh --all`
- main-side dispatch wrapper:
  - `./control-plane/scripts/collab_dispatch.sh --assignment-ref ASSIGN_... --payload-ref control-plane/collaboration/collab-model.yaml`
- main-side batch dispatch wrapper:
  - `./control-plane/scripts/collab_dispatch_batch.sh --agent-ref AGENT_KIMI --count 2`
  - dispatch instances are explicit and monotonic per checkbox lane:
    - assignment id: `ASSIGN_PHASE<NN>_<CHECKBOXTOKEN>_<AGENTTAG>_I<NN>`
    - message id: `MSG_PHASE<NN>_<CHECKBOXTOKEN>_<AGENTTAG>_I<NN>_DISPATCH`
    - branch: `phase<NN>.<checkbox>.i<NN>`
- atomic create+dispatch wrapper (for new assignments):
  - `./control-plane/scripts/collab_create_assignment.sh --assignment-id ASSIGN_... --agent-ref AGENT_KIMI --checkbox-ref AY1.2 --branch phase34.ay1.2 --payload-ref AGENTS.md`
- owner delegation wrapper (effective ownership handoff/revoke):
  - `./control-plane/scripts/collab_delegate_worktree.sh --worktree /home/andrey/src/cicsc/worktrees/kimi --owner-agent-ref AGENT_MAIN --delegate-to AGENT_KIMI`
- single-step worker loop helper (claim + fulfillment guidance):
  - `./control-plane/scripts/collab_run_once.sh --worktree "$WORKTREE"`
- acknowledge next actionable message:
  - `./control-plane/scripts/collab_claim_next.sh --worktree "$WORKTREE"`
  - one-command claim+commit: `./control-plane/scripts/collab_claim_next.sh --worktree "$WORKTREE" --commit`
  - override WIP guard only when necessary: `./control-plane/scripts/collab_claim_next.sh --worktree "$WORKTREE" --force`
- fulfill message with typed evidence (digest auto-computed):
  - `./control-plane/scripts/collab_fulfill.sh --message-ref MSG_... --worktree "$WORKTREE" --script scripts/check_x.sh --gate-report docs/pilot/report.json`
  - lazy re-run support for expensive checks:
    - `./control-plane/scripts/collab_fulfill.sh --message-ref MSG_... --worktree "$WORKTREE" --with scripts/check_x.sh --auto-report --lazy`
  - auto-commit with custom message:
    - `./control-plane/scripts/collab_fulfill.sh --message-ref MSG_... --worktree "$WORKTREE" --script scripts/check_x.sh --gate-report docs/pilot/report.json --auto-commit --commit-subject "phaseXX ayY.Y fulfill ..."`
- worktree status summary + recommended next action:
  - `./control-plane/scripts/collab_status.sh --worktree "$WORKTREE"`
- batch sweep mode:
  - `./control-plane/scripts/collab_sweep.sh --worktree "$WORKTREE" --with scripts/check_x.sh --auto-report --lazy`
- revert mistaken claim:
  - `./control-plane/scripts/collab_revert.sh --message-ref MSG_... --reason "claimed wrong assignment"`
- worker friction request (typed, immutable):
  - `./control-plane/scripts/collab_request_friction.sh --worktree "$WORKTREE" --type ergonomics --severity medium --summary "..." --repro-step "..."`
- main friction triage:
  - `./control-plane/scripts/collab_triage_friction.sh --message-ref MSG_... --decision accept_now --notes "..."`
- assignment-level delta view:
  - `./control-plane/scripts/collab_diff.sh --assignment-ref ASSIGN_...`
- aggregate history summary:
  - `./control-plane/scripts/collab_summary.sh --worktree "$WORKTREE" --since 2026-02-13`
- interactive loop wrapper:
  - `./control-plane/scripts/collab_interactive.sh --worktree "$WORKTREE"`
- fuzzy interactive picker (requires `fzf`):
  - `./control-plane/scripts/collab_fzf.sh --worktree "$WORKTREE"`
- main-side ingest+close wrapper:
  - `./control-plane/scripts/collab_close_ingested.sh --message-ref MSG_... --commit <sha>`
  - batch: `./control-plane/scripts/collab_close_batch.sh --agent-ref AGENT_KIMI --status fulfilled --count 0`
- stale mailbox watcher (warn/fail thresholds):
  - `./control-plane/scripts/collab_stale_watch.sh --warn-hours 24 --fail-hours 72`
- worker wait regime (poll + wake on actionable):
  - `./control-plane/scripts/collab_wait_for_messages.sh --worktree "$WORKTREE" --interval-seconds 5`
  - optional auto-process:
    - `./control-plane/scripts/collab_wait_for_messages.sh --worktree "$WORKTREE" --interval-seconds 5 --run-on-found "./control-plane/scripts/collab_process_messages.sh --role worker --worktree $WORKTREE"`
- assignment obligation/evidence delta view:
  - `./control-plane/scripts/collab_show_assignment.sh --ref ASSIGN_...`
- unified dry-run wrapper:
  - `./control-plane/scripts/collab_dry_run.sh <create|claim-next|fulfill|close|dispatch|delegate|append-event> ...`
- collab/view commit wrapper:
  - `./control-plane/scripts/collab_commit_views.sh --subject "governance/collab: ..."`

Happy path:
1. `./control-plane/scripts/collab_help.sh --role worker --worktree "$PWD"`
2. `./control-plane/scripts/collab_run_once.sh --worktree "$PWD"`
3. Execute required scripts and generate required artifacts for the claimed message.
4. `./control-plane/scripts/collab_fulfill.sh --message-ref MSG_... --worktree "$PWD" --script <script> --gate-report <report>`
5. Main ingests/closes via `./control-plane/scripts/collab_close_ingested.sh --message-ref MSG_... --commit <sha>`.

Canonical worker loop (multi-assignment):
1. `./control-plane/scripts/collab_status.sh --worktree "$WORKTREE"`
2. If `in_progress` is non-empty, fulfill the acknowledged message before any new claim.
3. Else claim next actionable: `./control-plane/scripts/collab_claim_next.sh --worktree "$WORKTREE"`.
4. Generate required evidence and fulfill:
   - `./control-plane/scripts/collab_fulfill.sh --message-ref MSG_... --worktree "$WORKTREE" --script <script> --gate-report <report> --suggest-commit`
5. Main ingests/closes fulfilled message:
   - `./control-plane/scripts/collab_close_ingested.sh --message-ref MSG_... --commit <sha>`
6. Repeat until `next_action=idle`.
7. If canonical sync/view drift appears in gates:
   - `./control-plane/scripts/collab_sync.sh`

WIP semantic rule (mechanically enforced):
- A worktree may not claim new `sent/queued` work while any message remains `acknowledged` in that same worktree.
- Override is exceptional and explicit: `collab_claim_next.sh --force`.

### 1. Preserve invariants before adding features
Never add functionality that weakens:
- transactional semantics
- replay-verification guarantees
- conformance between oracle and SQL backends

If a feature cannot be implemented without weakening invariants, add:
- a typechecker restriction, or
- an explicit limitation in docs/spec.

---

### 2. Always add a conformance test for new lowering logic
If you implement any of the following:

- Query → SQL lowering
- Expr → SQL lowering
- Constraint lowering
- Reducer lowering

Then also add:

- a differential test: SQL execution vs oracle interpreter

No exceptions. If you cannot write the test, the feature is not done.

---

### 3. Do not encode bundle-specific logic in runtime
The runtime must not “know” about:
- Ticketing
- CRM
- Kanban
- any specific shadow column names

All schema, columns, indexes, and views must come from IR.

If you find yourself hardcoding column names, stop and move that logic into:
`adapters/sqlite/src/schema/gen.ts` or equivalent.

---

### 4. Fail fast at compile-time, not at runtime
Prefer:

- IR typechecker rejections
- Spec compiler errors

over:

- runtime exceptions
- SQL errors
- silent NULL propagation

If something can be detected statically, detect it statically.

---

### 5. Respect the semantic split

There are three layers. Do not collapse them:

1. **Spec DSL (user intent)**
   - ergonomic
   - may contain sugar
   - no backend assumptions

2. **Core IR (semantic truth)**
   - minimal calculus
   - backend-agnostic
   - must be fully typechecked

3. **Backend lowering**
   - SQL-specific
   - may reject unsupported constructs
   - must conform to oracle semantics

Never leak backend constraints into Spec or Core IR.
Enforce backend limits via typechecker flags or feature gates.

---

### 6. Add migrations only after type safety is strong
Do not implement migration execution until:

- IR typechecker is strict
- schema generation is deterministic
- replay verification is stable

Migrations amplify errors. They must be built on solid ground.

---

## Execution Order (Recommended)

Follow this order unless blocked:

1. IR typechecker hardening  
2. Schema generation completeness (indexes, per-version tables)  
3. SQL lowering completeness + conformance tests  
4. Bundle registry (R2/KV) + tenant binding  
5. Spec DSL sugar + compiler  
6. Migrations + cutover protocol  
7. Postgres adapter  
8. Stress verticals (CRM, Kanban)  

Do not skip steps. Each step reduces blast radius for the next.

---

## Testing Discipline

Every PR should add or extend at least one of:

- oracle tests
- SQL-vs-oracle conformance tests
- IR typechecker negative tests
- schema generation snapshot tests

If a change cannot be tested meaningfully, explain why in the PR.

---

## Error Handling Philosophy

Prefer:

- explicit errors
- structured error objects
- path-qualified error messages

Avoid:

- stringly-typed errors
- silent fallback behavior
- partial success

---

## Design Smells (Stop If You See These)

- “Let’s special-case Ticketing here”
- “We’ll just allow this expression in SQL”
- “Let’s parse SQL back into IR”
- “We can fix this at runtime”
- “This migration is best-effort”

Each of these breaks core invariants.

---

## Definition of Done (for any TODO)

A TODO is complete only when:

- Code is implemented
- Typechecker updated (if semantics changed)
- Conformance tests added or updated
- Docs/spec updated if semantics changed
- No bundle-specific hacks introduced

---

## North Star

At completion, CICSC should allow:

> A non-programmer to describe a socio-technical control system in Spec,
> compile it, deploy it, evolve it with migrations,
> and retain invariants provably across time.

Everything you build should move the system toward that state.
