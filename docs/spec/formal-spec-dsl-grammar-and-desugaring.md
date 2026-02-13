# Spec DSL Grammar and Desugaring Rules (v0)

## Frozen v1 Contract Artifact

Phase 5 freezes a canonical compiler contract artifact:

- Fixture: `spec/contracts/spec-dsl-v1.fixture.json`
- Expected IR: `spec/contracts/spec-dsl-v1.ir.json`
- Gate test: `tests/spec/spec-dsl-v1-freeze.test.ts`

Any intentional DSL grammar/desugaring change must update these artifacts in the
same change that updates compiler logic.

## Grammar (shape-level)

```
Spec :=
  { version:0
  , entities: { EntityName: EntitySpec+ }
  , policies?: PolicyMap
  , constraints?: ConstraintMap
  , views?: ViewMap
  , slas?: SlaMap
  , migrations?: MigrationMap
  }
```

EntitySpec includes:

- states, initial
- attributes/shadows
- commands
- reducers

## Guard Sugar Desugaring

- `state_is: "X"` -> `eq(var(state), lit("X"))`
- `role_is: "R"` -> `call(has_role, [var(actor), lit("R")])`
- `all:[g1,g2]` -> `and([D(g1), D(g2)])`
- `any:[g1,g2]` -> `or([D(g1), D(g2)])`

Where `D` is desugaring function.

## Reducer Sugar Desugaring

- `set_state: "done"` -> `set_state({expr: lit("done")})`
- `set_attr:{field:f,value:v}` -> `set_attr({name:f,expr:Wrap(v)})`
- `set_shadow:{field:f,value:v}` -> `set_shadow({name:f,expr:Wrap(v)})`

## View Sugar Desugaring

`lanes` block desugars to Query pipeline:

1. filter on states (if provided)
2. order_by on lane sort key
3. limit

## Auth Mapping Desugaring

Command `auth.policy = P` contributes:

`guard := and(original_guard, call(auth_ok, [actor, "P"]))`
