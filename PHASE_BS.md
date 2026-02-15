# Phase BS: Rich Aggregates in Views

**Status**: PLANNED (v1.8.0)  
**Agent**: TBD  
**Vertical Gap**: Rate/ratio operators missing

## Problem

Current: Basic aggregations only
```python
aggregate {
  total: count()
  sum: sum(amount)
}
```

Gap: Time-series calculations
```python
aggregate {
  resolved_per_day: rate(event Resolved, "1d")
  avg_resolution: avg(time_between(Created, Resolved))
  satisfaction: ratio(Positive, Total)
}
```

## Core IR

```typescript
export type AggExprV0 =
  | { count: { expr?: { value: ExprV0 } } }
  | { sum: { expr: ExprV0 } }
  | { rate: { event: string; window: string } }      // NEW
  | { ratio: { numerator: ExprV0; denominator: ExprV0 } }  // NEW
  | { time_between: { start: string; end: string } }  // NEW
```

## Milestones

### BS1: Query AST Extension
- [x] BS1.1: Add rate operator
- [x] BS1.2: Add ratio operator
- [x] BS1.3: Add time_between operator
- [x] BS1.4: Update QueryV0 types

### BS2: View Runtime
- [x] BS2.1: SQL generation for rate()
- [x] BS2.2: SQL generation for ratio()
- [x] BS2.3: Oracle conformance
- [x] BS2.4: Spec DSL sugar
