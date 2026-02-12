# Spec DSL Teaching Material

## Lesson 1: Entities and States

- define `entities`, `states`, `initial`
- exercise: model a 3-state workflow

## Lesson 2: Commands and Reducers

- map intents to emitted events
- write deterministic reducer ops
- exercise: add transition command + reducer

## Lesson 3: Views and Constraints

- lanes view sugar
- snapshot vs bool_query constraints
- exercise: implement WIP limit

## Lesson 4: Policies and Auth Mapping

- policy DSL basics
- per-command auth mapping
- exercise: restrict one command to manager role

## Lesson 5: Migrations and Verification

- migration transform/state map
- replay verification workflow
- exercise: rename an event with migration edge
