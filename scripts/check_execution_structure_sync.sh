#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
import sqlite3

conn = sqlite3.connect("state/ledger.db")
conn.row_factory = sqlite3.Row
cur = conn.cursor()

errors = []

cur.execute(
    """
    SELECT m.id
    FROM milestones m
    LEFT JOIN phases p ON p.id = m.phase_id
    WHERE p.id IS NULL
    """
)
missing_phase = [row["id"] for row in cur.fetchall()]
if missing_phase:
    errors.append(f"milestones missing phase linkage: {missing_phase}")

cur.execute(
    """
    SELECT c.id
    FROM checkboxes c
    LEFT JOIN milestones m ON m.id = c.milestone_id
    WHERE m.id IS NULL
    """
)
missing_milestone = [row["id"] for row in cur.fetchall()]
if missing_milestone:
    errors.append(f"checkboxes missing milestone linkage: {missing_milestone}")

cur.execute("SELECT COUNT(*) AS n FROM phases")
phase_count = int(cur.fetchone()["n"])
cur.execute("SELECT COUNT(*) AS n FROM milestones")
milestone_count = int(cur.fetchone()["n"])
cur.execute("SELECT COUNT(*) AS n FROM checkboxes")
checkbox_count = int(cur.fetchone()["n"])

if phase_count == 0 or milestone_count == 0 or checkbox_count == 0:
    errors.append("phase/milestone/checkbox tables must be non-empty")

if errors:
    print("execution structure sync check failed")
    for err in errors:
        print(f"- {err}")
    raise SystemExit(1)

print("execution structure sync check passed")
PY
