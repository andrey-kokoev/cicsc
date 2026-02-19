#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="diagnose"
APPLY=0

if [[ $# -gt 0 && "${1:-}" != --* ]]; then
    MODE="$1"
    shift
fi
while [[ $# -gt 0 ]]; do
    case "$1" in
        --apply) APPLY=1; shift ;;
        --dry-run) APPLY=0; shift ;;
        --help|-h)
            echo "Usage:"
            echo "  $0 diagnose"
            echo "  $0 repair [--dry-run|--apply]"
            exit 0
            ;;
        *)
            echo "Unknown arg: $1" >&2
            exit 1
            ;;
    esac
done

if [[ "$MODE" != "diagnose" && "$MODE" != "repair" ]]; then
    echo "Unknown mode: $MODE" >&2
    exit 1
fi

python3 - "$MODE" "$APPLY" << 'PY'
import sys
import sqlite3
from pathlib import Path

mode = sys.argv[1]
apply_changes = bool(int(sys.argv[2]))

db_path = Path("state/ledger.db")
conn = sqlite3.connect(str(db_path))
conn.row_factory = sqlite3.Row
cur = conn.cursor()

def q(sql, args=()):
    cur.execute(sql, args)
    return cur.fetchall()

issues = []
ops = []

# 1) assignments referencing missing checkbox
rows = q("""
SELECT a.checkbox_ref, a.agent_ref, a.status
FROM assignments a
LEFT JOIN checkboxes c ON c.id = a.checkbox_ref
WHERE c.id IS NULL
""")
for r in rows:
    issues.append(
        f"orphan assignment: checkbox={r['checkbox_ref']} agent={r['agent_ref']} status={r['status']}"
    )
    ops.append(("DELETE FROM assignments WHERE checkbox_ref = ?", (r["checkbox_ref"],), "delete orphan assignment"))

# 2) checkbox done but has active assignment
rows = q("""
SELECT c.id
FROM checkboxes c
JOIN assignments a ON a.checkbox_ref = c.id
WHERE c.status = 'done' AND a.status = 'assigned'
""")
for r in rows:
    issues.append(f"done checkbox has active assignment: {r['id']}")
    ops.append((
        "UPDATE assignments SET status = 'done', completed_at = COALESCE(completed_at, datetime('now')) WHERE checkbox_ref = ? AND status = 'assigned'",
        (r["id"],),
        "mark assignment done for done checkbox",
    ))

# 3) checkbox open but has done assignment
rows = q("""
SELECT c.id
FROM checkboxes c
JOIN assignments a ON a.checkbox_ref = c.id
WHERE c.status = 'open' AND a.status = 'done'
""")
for r in rows:
    issues.append(f"open checkbox has done assignment: {r['id']}")
    ops.append(("UPDATE checkboxes SET status = 'done' WHERE id = ?", (r["id"],), "mark checkbox done from assignment"))

# 4) multiple active assignments for same checkbox
rows = q("""
SELECT checkbox_ref, COUNT(*) as cnt
FROM assignments
WHERE status = 'assigned'
GROUP BY checkbox_ref
HAVING COUNT(*) > 1
""")
for r in rows:
    issues.append(f"multiple active assignments: {r['checkbox_ref']} ({r['cnt']})")
    extra = q("""
        SELECT rowid
        FROM assignments
        WHERE checkbox_ref = ? AND status = 'assigned'
        ORDER BY created_at DESC
    """, (r["checkbox_ref"],))
    for e in extra[1:]:
        ops.append(("DELETE FROM assignments WHERE rowid = ?", (e["rowid"],), "drop duplicate active assignment"))

if not issues:
    print("Doctor: no issues found")
    conn.close()
    raise SystemExit(0)

print("Doctor: issues detected")
for issue in issues:
    print(f"  - {issue}")

if mode == "diagnose":
    print("\nRun 'control-plane/doctor.sh repair --dry-run' to preview fixes.")
    conn.close()
    raise SystemExit(1)

print("\nPlanned repairs:")
for sql, args, label in ops:
    print(f"  - {label}: {sql} {tuple(args)}")

if not apply_changes:
    print("\nDry-run only; no changes applied.")
    conn.close()
    raise SystemExit(0)

for sql, args, _ in ops:
    cur.execute(sql, args)
conn.commit()
print("\nApplied repairs.")
conn.close()
PY
