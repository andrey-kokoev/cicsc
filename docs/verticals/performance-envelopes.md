# Performance Envelopes (Reference Baselines)

These envelopes define reference operating bands for local development runs.

| Vertical   | Commands/s (single tenant) | p95 write latency | p95 view latency |
|------------|-----------------------------|-------------------|------------------|
| Kanban v1  | 120 - 300 ops/s             | 8 - 25 ms         | 5 - 20 ms        |
| Ticketing v1 | 100 - 250 ops/s           | 10 - 30 ms        | 6 - 22 ms        |
| CRM v1     | 90 - 220 ops/s              | 12 - 35 ms        | 7 - 25 ms        |

## Notes

- Envelope values are intended for regression detection, not hard SLO commitments.
- Measurements assume local SQLite-backed harness with warm cache.
- Backend conformance must hold even when throughput differs by adapter.
