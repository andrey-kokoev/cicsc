#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
import sqlite3
import subprocess

conn = sqlite3.connect("state/ledger.db")
conn.row_factory = sqlite3.Row
cur = conn.cursor()

cur.execute(
    """
    SELECT a.checkbox_ref, a.commit_sha
    FROM assignments a
    JOIN checkboxes c ON c.id = a.checkbox_ref
    WHERE a.status = 'done' AND c.status = 'done'
    ORDER BY a.checkbox_ref
    """
)
rows = [dict(r) for r in cur.fetchall()]

errors = []
for row in rows:
    checkbox = str(row["checkbox_ref"])
    commit = str(row["commit_sha"] or "").strip()
    if not commit:
        errors.append(f"missing commit evidence for done checkbox {checkbox}")
        continue

    run = subprocess.run(
        ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
        cwd=".",
        capture_output=True,
        text=True,
        check=False,
    )
    if run.returncode != 0:
        errors.append(f"commit evidence not found in git object db for {checkbox}: {commit}")

if errors:
    print("checkbox commit evidence (sqlite ledger) check failed")
    for err in errors:
        print(f"- {err}")
    raise SystemExit(1)

print("checkbox commit evidence (sqlite ledger) check passed")
PY
