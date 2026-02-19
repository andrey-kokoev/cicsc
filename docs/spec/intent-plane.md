# Intent Plane Contract v1

## Purpose

Define the pre-compile interaction layer where users describe systems in natural language and the assistant shapes that intent into Spec JSON (`SpecV0`) before Core IR compilation.

This contract is for the **intent-plane** only. Formal system semantics remain in Spec/Core IR.

## Decisions (Locked)

1. Internal representation: `InterviewState` only (no external intent schema).
2. Formalization boundary: Spec/Core IR is the formal intent artifact.
3. Ambiguity posture: infer aggressively by default.
4. Approval: optional.
5. Interview output target: Spec JSON (`SpecV0`) canonical.
6. Scope: full chat-driven editing across Core IR-relevant semantics.
7. Incomplete intent handling: emit draft but mark non-deployable until gaps resolved.
8. Enforcement location: assistant code only.

## Existing Contracts to Reuse

- Interview state/types: `core/assistant/interview-engine.ts`
- Natural language to draft representation: `core/assistant/interview-engine.ts`
- Translation layer: `core/assistant/translate.ts`
- Refinement primitives: `core/assistant/refinement.ts`
- Spec parse/type validation: `spec/parse-yaml.ts`, `spec/typecheck.ts`
- Core IR target schema: `docs/spec/core-ir-schema.json`

## v1 Editing Scope

Post-greenfield editing is in scope across the full Core IR-facing surface.
This includes additive and non-additive edits such as field/state/entity changes,
renames, removals, and broader structural updates.

Intent-plane remains responsible for producing a draft plus explicit blocking
issues when safety/completeness cannot be established.

## Intent-Plane Output Rules

- Canonical output is machine-readable Spec JSON (`SpecV0` shape).
- A single constructor path should produce canonical Spec JSON (no parallel Spec constructors).
- DSL text can be emitted as presentation/preview but is non-canonical.
- Any unresolved semantic gap must be surfaced in a blocking issue list.
- Blocked drafts are allowed artifacts; deployment from blocked drafts is not.

## Implementation Checklist (Mapped)

1. Add explicit completeness gate in assistant output object.
   - File: `core/assistant/interview-engine.ts`
   - Add: `blockingIssues: string[]` on state/result.
   - Rule: non-empty `blockingIssues` => non-deployable draft.

2. Make Spec JSON the canonical translator output.
   - File: `core/assistant/translate.ts`
   - Add: `translateToSpecJson(state): SpecV0`.
   - Keep DSL generation as optional preview helper.

3. Support full edit-intent detection in refinement engine.
   - File: `core/assistant/refinement.ts`
   - Detect: additive + non-additive edit intents (including rename/remove).
   - Never hard-reject by category; route unsafe/incomplete edits to `blockingIssues`.

4. Add intent-plane validation pass before compile.
   - Files: `core/assistant/*` integration point + `spec/typecheck.ts` caller path.
   - Rule: if `blockingIssues.length > 0`, return draft + issues, skip compile/install path.

5. Add tests for v1 contract.
   - New tests under: `tests/spec/` (or `tests/core/assistant/` if added).
   - Cases:
     - greenfield interview -> valid Spec JSON
     - additive and non-additive refinements are parsed and routed
     - unresolved gaps produce blocked draft
     - unsupported phrasing produces explicit clarification requests

## Non-Goals

- New intent JSON schema.
- New persistence format for interview state.
- Runtime/control-plane enforcement changes for intent-plane policy.
