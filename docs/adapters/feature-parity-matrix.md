# Backend Feature Parity Matrix

| Feature | SQLite | Postgres | oracle (JS) |
|---------|--------|----------|-------------|
| JOINS   | Full   | Full     | Full        |
| JSON    | TEXT   | JSONB    | Object      |
| BIGINT  | INTEGER| BIGINT   | Number      |
| WHERE   | Numeric| Boolean  | Boolean     |
| WINDOW  | Limited| Native   | N/A         |
| ATOM_TX | Full   | Full     | N/A         |

## Notes

- **SQLite**: Booleans are stored as `0/1`. Lowering uses `CASE WHEN` to simulate boolean expressions in non-filtering contexts.
- **Postgres**: Uses native `BOOLEAN` and `JSONB` for performance and correctness. `RETURNING` optimized for event appending.
- **oracle**: The gold standard for semantic correctness. All backends must conform via differential tests.
