#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ERRORS=0
AUTO_PROMOTED=0

echo "Validating execution ledger..."
python3 << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_all_checkboxes

errors = []

checkboxes = get_all_checkboxes()

seen_checkboxes = set()
for cb in checkboxes:
    cid = cb["id"]
    if cid in seen_checkboxes:
        errors.append(f"Duplicate checkbox: {cid}")
    seen_checkboxes.add(cid)
    
    status = cb["status"]
    if status not in ("open", "done"):
        errors.append(f"Invalid status for {cid}: {status}")

if errors:
    for e in errors:
        print(f"  ERROR: {e}", file=sys.stderr)
    sys.exit(1)
print(f"  Ledger structure: OK ({len(checkboxes)} checkboxes)")
PY

if [[ $? -ne 0 ]]; then
    ERRORS=$((ERRORS + 1))
fi

echo "Validating assignments..."
python3 << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_all_checkboxes, get_all_assignments

checkboxes = get_all_checkboxes()
valid_checkboxes = {cb["id"] for cb in checkboxes}
assignments = get_all_assignments()

errors = []
active_checkboxes = set()

for a in assignments:
    cb = a["checkbox_ref"]
    status = a["status"]
    agent = a["agent_ref"]
    
    if cb not in valid_checkboxes:
        errors.append(f"Invalid checkbox_ref: {cb}")
        continue
        
    if status not in ("open", "in_progress", "done"):
        errors.append(f"Invalid status for {cb}: {status}")
        
    if status in ("open", "in_progress"):
        if cb in active_checkboxes:
            errors.append(f"Multiple active assignments for {cb}")
        active_checkboxes.add(cb)

for cb in checkboxes:
    if cb["status"] == "done" and cb["id"] in active_checkboxes:
        errors.append(f"Checkbox {cb['id']} is done but has active assignment")

if errors:
    for e in errors:
        print(f"  ERROR: {e}", file=sys.stderr)
    sys.exit(1)
print(f"  Assignments: OK ({len(assignments)} total)")
PY

if [[ $? -ne 0 ]]; then
    ERRORS=$((ERRORS + 1))
fi

echo "Checking for auto-promotion..."
AUTO_PROMOTED=$(python3 << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_all_phases, get_phase_checkbox_stats, update_phase_status

promoted = []

for ph in get_all_phases():
    stats = get_phase_checkbox_stats(ph["id"])
    if stats["total"] > 0 and stats["done"] == stats["total"] and ph["status"] != "complete":
        update_phase_status(ph["id"], "complete")
        promoted.append(ph["id"])

for pid in promoted:
    print(f"  Auto-promoted {pid} -> complete")

print(len(promoted))
PY
)

if [[ $ERRORS -eq 0 ]]; then
    if [[ $AUTO_PROMOTED -gt 0 ]]; then
        echo "Validation passed ($AUTO_PROMOTED phase(s) auto-promoted)"
    else
        echo "Validation passed"
    fi
    exit 0
else
    echo "Validation failed with $ERRORS error(s)" >&2
    exit 1
fi
