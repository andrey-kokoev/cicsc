# Annotated Canonical Vertical Examples

## Kanban

- Spec: `verticals/kanban/spec.v1.json`
- Notes:
  - lane transitions via reducer fold
  - WIP invariant via bool_query
  - row_policy + command auth usage

## Ticketing

- Spec: `verticals/ticketing/spec.v1.json`
- Notes:
  - escalation and closure paths
  - SLA declarations (`first_response`, `time_to_resolution`)
  - assignee/priority modeling

## CRM

- Spec: `verticals/crm/spec.v1.json`
- Notes:
  - stage progression and ownership
  - conversion signal materialization
  - owner-level aggregate view
