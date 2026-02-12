# Reference Implementation Walkthroughs

## Walkthrough 1: Spec -> Bundle

- parse Spec DSL
- spec typecheck
- compile to Core IR
- IR typecheck

## Walkthrough 2: Command Execution

- load tenant bundle/version
- guard evaluation
- tx append + reducer fold
- constraints + SLA checks
- snapshot write + receipt

## Walkthrough 3: Migration and Cutover

- transform history
- replay verification
- pause/migrate/resume cutover
