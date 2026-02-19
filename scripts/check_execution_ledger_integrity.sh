#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
import re
import sqlite3

conn = sqlite3.connect("state/ledger.db")
conn.row_factory = sqlite3.Row
cur = conn.cursor()

phase_id_re = re.compile(r'^[A-Z]{1,3}$')
milestone_id_re = re.compile(r'^[A-Z]{1,3}\d+$')
checkbox_id_re = re.compile(r'^[A-Z]{1,4}\d+\.\d+$')

errors = []

cur.execute("SELECT COUNT(*) AS n FROM phases")
if int(cur.fetchone()["n"]) == 0:
    errors.append("sqlite ledger has no phases")

cur.execute("SELECT id, number, status, title FROM phases")
for row in cur.fetchall():
    pid = str(row["id"] or "")
    if not phase_id_re.match(pid):
        errors.append(f"invalid phase id: {pid}")
    if row["number"] is None:
        errors.append(f"phase {pid} missing number")
    if str(row["status"] or "") not in {"planned", "in_progress", "complete", "deferred"}:
        errors.append(f"phase {pid} has invalid status: {row['status']}")
    if not str(row["title"] or "").strip():
        errors.append(f"phase {pid} missing title")

cur.execute(
    """
    SELECT m.id
    FROM milestones m
    LEFT JOIN phases p ON p.id = m.phase_id
    WHERE p.id IS NULL
    """
)
for row in cur.fetchall():
    errors.append(f"milestone has missing phase linkage: {row['id']}")

cur.execute("SELECT id, phase_id, title FROM milestones")
for row in cur.fetchall():
    mid = str(row["id"] or "")
    if not milestone_id_re.match(mid):
        errors.append(f"invalid milestone id: {mid}")
    if not str(row["phase_id"] or "").strip():
        errors.append(f"milestone {mid} missing phase_id")
    if not str(row["title"] or "").strip():
        errors.append(f"milestone {mid} missing title")

cur.execute(
    """
    SELECT c.id
    FROM checkboxes c
    LEFT JOIN milestones m ON m.id = c.milestone_id
    WHERE m.id IS NULL
    """
)
for row in cur.fetchall():
    errors.append(f"checkbox has missing milestone linkage: {row['id']}")

cur.execute("SELECT id, milestone_id, status, description FROM checkboxes")
for row in cur.fetchall():
    cid = str(row["id"] or "")
    if not checkbox_id_re.match(cid):
        errors.append(f"invalid checkbox id: {cid}")
    if not str(row["milestone_id"] or "").strip():
        errors.append(f"checkbox {cid} missing milestone_id")
    if str(row["status"] or "") not in {"open", "done"}:
        errors.append(f"invalid checkbox status for {cid}: {row['status']}")
    if not str(row["description"] or "").strip():
        errors.append(f"checkbox {cid} missing description")

cur.execute(
    """
    SELECT a.checkbox_ref
    FROM assignments a
    LEFT JOIN checkboxes c ON c.id = a.checkbox_ref
    WHERE c.id IS NULL
    """
)
for row in cur.fetchall():
    errors.append(f"assignment has missing checkbox linkage: {row['checkbox_ref']}")

cur.execute(
    """
    SELECT a.checkbox_ref, a.agent_ref
    FROM assignments a
    LEFT JOIN agents ag ON ag.id = a.agent_ref
    WHERE ag.id IS NULL
    """
)
for row in cur.fetchall():
    errors.append(f"assignment {row['checkbox_ref']} has missing agent linkage: {row['agent_ref']}")

if errors:
    print("execution-ledger integrity check failed")
    for err in errors:
        print(f"- {err}")
    raise SystemExit(1)

print("execution-ledger integrity check passed")
PY
