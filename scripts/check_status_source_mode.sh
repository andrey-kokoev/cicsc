#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
import sqlite3
from pathlib import Path

root = Path('.')
db_path = root / 'state/ledger.db'
if not db_path.exists():
    print('status source mode check failed')
    print(f'- missing sqlite runtime store: {db_path}')
    raise SystemExit(1)

conn = sqlite3.connect(db_path)
cur = conn.cursor()
cur.execute("SELECT name FROM sqlite_master WHERE type='table'")
tables = {row[0] for row in cur.fetchall()}
required = {'phases', 'milestones', 'checkboxes', 'assignments', 'agents', 'events'}
missing = sorted(required - tables)

if missing:
    print('status source mode check failed')
    print(f'- sqlite canonical schema missing tables: {missing}')
    raise SystemExit(1)

print('status source mode check passed (sqlite_db_canonical)')
PY
