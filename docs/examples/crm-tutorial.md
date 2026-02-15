# Tutorial: CRM with Schema Evolution

This tutorial demonstrates how to evolve a CRM system using CICSC migrations.

## Phase 1: Basic Lead Management

```cicsc
version 1

entity Lead:
    states: [New, Contacted, Qualified, Dead]
    initial: New
    attr name: string
```

## Phase 2: Adding Mandatory Details (Breaking Change)

Business requirements change. Now we must collect an email address for every qualified lead.

### Update the Spec
```cicsc
version 2

entity Lead:
    states: [New, Contacted, Qualified, Dead]
    attr name: string
    attr email: string // Now mandatory
```

### Generate Migration

Running `cicsc diff v1 v2` will detect that `email` is a new mandatory field, which is a **Breaking Change** for existing data.

Create a migration spec `migration_v1_v2.json`:

```json
{
  "from_version": 1,
  "to_version": 2,
  "event_transforms": {
    "LeadCreated": {
      "payload_map": {
        "name": "src.name",
        "email": "pending@example.com"
      }
    }
  }
}
```

### Apply Migration

1. **Dry-Run**: `cicsc migrate run --dry-run migration_v1_v2.json`
2. **Snapshot**: System automatically creates `snapshots_v1_backup`.
3. **Replay**: All historical `LeadCreated` events are re-run, mapping the new `email` field.
4. **Verify**: Invariants are checked against the new v2 schema.

## Summary

CICSC ensures that your "Qualified" leads from v1 still meet the "Qualified" criteria in v2, or warns you if the data transformation is insufficient.
