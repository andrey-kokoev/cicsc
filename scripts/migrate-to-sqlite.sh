#!/usr/bin/env bash
#==============================================================================
# migrate-to-sqlite.sh - Historical migration stub
#==============================================================================

set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "SQLite is already canonical; YAML migration is retired."

python3 - << 'PY'
import sqlite3

conn = sqlite3.connect("state/ledger.db")
cur = conn.cursor()

required = {"phases", "milestones", "checkboxes", "assignments", "agents", "events"}
cur.execute("SELECT name FROM sqlite_master WHERE type='table'")
tables = {row[0] for row in cur.fetchall()}
missing = sorted(required - tables)

if missing:
    print("ERROR: sqlite schema is incomplete")
    print(f"missing tables: {missing}")
    raise SystemExit(1)

for table in ("phases", "milestones", "checkboxes", "assignments", "agents"):
    cur.execute(f"SELECT COUNT(*) FROM {table}")
    count = int(cur.fetchone()[0])
    print(f"{table}: {count}")

print("No migration required.")
PY
