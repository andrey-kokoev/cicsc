#!/usr/bin/env bash
#==============================================================================
# migrate-to-sqlite.sh - Migrate control-plane YAML to SQLite
#==============================================================================

set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3 << 'PY'
import sqlite3
import yaml

conn = sqlite3.connect('state/ledger.db')
cur = conn.cursor()

cur.execute('''CREATE TABLE IF NOT EXISTS phases (
    id TEXT PRIMARY KEY,
    number INTEGER,
    status TEXT CHECK(status IN ('planned','in_progress','complete','deferred')),
    title TEXT,
    description TEXT
)''')

cur.execute('''CREATE TABLE IF NOT EXISTS milestones (
    id TEXT PRIMARY KEY,
    phase_id TEXT REFERENCES phases(id),
    title TEXT
)''')

cur.execute('''CREATE TABLE IF NOT EXISTS checkboxes (
    id TEXT PRIMARY KEY,
    milestone_id TEXT REFERENCES milestones(id),
    status TEXT CHECK(status IN ('open','done')),
    description TEXT
)''')

cur.execute('''CREATE TABLE IF NOT EXISTS assignments (
    checkbox_ref TEXT REFERENCES checkboxes(id),
    agent_ref TEXT,
    status TEXT CHECK(status IN ('assigned','done')),
    created_at TEXT,
    started_at TEXT,
    commit_sha TEXT,
    completed_at TEXT,
    PRIMARY KEY (checkbox_ref)
)''')

cur.execute('''CREATE TABLE IF NOT EXISTS events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    type TEXT,
    checkbox_ref TEXT,
    agent_ref TEXT,
    timestamp TEXT,
    details TEXT
)''')

conn.commit()
print("Database created. Now migrating YAML...")

def normalize_assignment_status(status):
    if status in ("open", "in_progress", "assigned"):
        return "assigned"
    if status == "done":
        return "done"
    return "assigned"

def normalize_checkbox_status(status):
    if status in ("open", "assigned"):
        # "assigned" moved to assignments table; keep checkbox open.
        return "open"
    if status == "done":
        return "done"
    return "open"

# Load YAML
with open('control-plane/execution-ledger.yaml') as f:
    ledger = yaml.safe_load(f)

# Migrate phases
for ph in ledger.get('phases', []):
    cur.execute("""
        INSERT OR REPLACE INTO phases (id, number, status, title, description)
        VALUES (?, ?, ?, ?, ?)
    """, (ph['id'], ph.get('number'), ph.get('status'), ph.get('title'), ph.get('description')))
    
    for ms in ph.get('milestones', []):
        cur.execute("""
            INSERT OR REPLACE INTO milestones (id, phase_id, title)
            VALUES (?, ?, ?)
        """, (ms['id'], ph['id'], ms.get('title')))
        
        for cb in ms.get('checkboxes', []):
            cur.execute("""
                INSERT OR REPLACE INTO checkboxes (id, milestone_id, status, description)
                VALUES (?, ?, ?, ?)
            """, (cb['id'], ms['id'], normalize_checkbox_status(cb.get('status')), cb.get('description')))

# Migrate assignments
try:
    with open('control-plane/assignments.yaml') as f:
        assignments = yaml.safe_load(f)
    
    for a in assignments.get('assignments', []):
        cur.execute("""
            INSERT OR REPLACE INTO assignments 
            (checkbox_ref, agent_ref, status, created_at, started_at, commit_sha, completed_at)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (a.get('checkbox_ref'), a.get('agent_ref'), normalize_assignment_status(a.get('status')),
              a.get('created_at'), a.get('started_at'), a.get('commit'), a.get('completed_at')))
except FileNotFoundError:
    print("No assignments.yaml found, skipping")

conn.commit()

# Verify counts
cur.execute("SELECT COUNT(*) FROM phases")
print(f"Phases: {cur.fetchone()[0]}")

cur.execute("SELECT COUNT(*) FROM milestones")
print(f"Milestones: {cur.fetchone()[0]}")

cur.execute("SELECT COUNT(*) FROM checkboxes")
print(f"Checkboxes: {cur.fetchone()[0]}")

cur.execute("SELECT COUNT(*) FROM assignments")
print(f"Assignments: {cur.fetchone()[0]}")

print("Migration complete!")
PY
