#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ERRORS=0
AUTO_PROMOTED=0

echo "Validating execution ledger..."
python3 << 'PY'
import yaml, sys
from pathlib import Path

ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())
errors = []

# Check phase/milestone/checkbox structure
seen_phases = set()
for ph in ledger.get("phases", []):
    pid = ph.get("id")
    if pid in seen_phases:
        errors.append(f"Duplicate phase: {pid}")
    seen_phases.add(pid)
    
    seen_milestones = set()
    for ms in ph.get("milestones", []):
        mid = ms.get("id")
        if mid in seen_milestones:
            errors.append(f"Duplicate milestone: {mid}")
        seen_milestones.add(mid)
        
        seen_checkboxes = set()
        for cb in ms.get("checkboxes", []):
            cid = cb.get("id")
            if cid in seen_checkboxes:
                errors.append(f"Duplicate checkbox: {cid}")
            seen_checkboxes.add(cid)
            
            status = cb.get("status")
            if status not in ("open", "done"):
                errors.append(f"Invalid status for {cid}: {status}")

if errors:
    for e in errors:
        print(f"  ERROR: {e}", file=sys.stderr)
    sys.exit(1)
print("  Ledger structure: OK")
PY

if [[ $? -ne 0 ]]; then
    ERRORS=$((ERRORS + 1))
fi

echo "Validating assignments..."
python3 << 'PY'
import yaml, sys, re
from pathlib import Path

ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())
assignments = yaml.safe_load(Path("control-plane/assignments.yaml").read_text())

# Detect manual edits
manual_edit_errors = []
for a in assignments.get("assignments", []):
    # Check for wrong field name (manual edit indicator)
    if "agent" in a and "agent_ref" not in a:
        manual_edit_errors.append(f"Assignment {a.get('checkbox_ref', '?')} uses 'agent' instead of 'agent_ref' - manual edit detected")
    
    # Check for missing required fields
    required = ["checkbox_ref", "agent_ref", "status"]
    for field in required:
        if field not in a:
            manual_edit_errors.append(f"Assignment {a.get('checkbox_ref', '?')} missing required field: {field}")
    
    # Check agent_ref format (must be uppercase with underscores)
    agent_ref = a.get("agent_ref", "")
    if agent_ref and not re.match(r'^AGENT_[A-Z_]+$', agent_ref):
        manual_edit_errors.append(f"Assignment {a['checkbox_ref']} has invalid agent_ref format: {agent_ref}")
    
    # Check status values
    status = a.get("status", "")
    if status and status not in ("open", "in_progress", "done", "deferred"):
        manual_edit_errors.append(f"Assignment {a.get('checkbox_ref', '?')} has invalid status: {status}")

if manual_edit_errors:
    for e in manual_edit_errors:
        print(f"  MANUAL EDIT DETECTED: {e}", file=sys.stderr)
    print("  Use dispatch.sh/claim.sh/complete.sh instead of manual edits", file=sys.stderr)
    sys.exit(1)

# Build set of valid checkboxes
valid_checkboxes = set()
for ph in ledger.get("phases", []):
    for ms in ph.get("milestones", []):
        for cb in ms.get("checkboxes", []):
            valid_checkboxes.add(cb["id"])

errors = []
active_checkboxes = set()

for a in assignments.get("assignments", []):
    cb = a.get("checkbox_ref")
    status = a.get("status")
    agent = a.get("agent_ref")
    
    if cb not in valid_checkboxes:
        errors.append(f"Invalid checkbox_ref: {cb}")
        continue
        
    if status not in ("open", "in_progress", "done"):
        errors.append(f"Invalid status for {cb}: {status}")
        
    if status in ("open", "in_progress"):
        if cb in active_checkboxes:
            errors.append(f"Multiple active assignments for {cb}")
        active_checkboxes.add(cb)

# Check ledger checkboxes marked done don't have active assignments
for ph in ledger.get("phases", []):
    for ms in ph.get("milestones", []):
        for cb in ms.get("checkboxes", []):
            if cb.get("status") == "done" and cb["id"] in active_checkboxes:
                errors.append(f"Checkbox {cb['id']} is done but has active assignment")

if errors:
    for e in errors:
        print(f"  ERROR: {e}", file=sys.stderr)
    sys.exit(1)
print(f"  Assignments: OK ({len(assignments.get('assignments', []))} total)")
PY

if [[ $? -ne 0 ]]; then
    ERRORS=$((ERRORS + 1))
fi

echo "Checking for auto-promotion..."
python3 << 'PY'
import yaml
from pathlib import Path

ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())
promoted = []

for ph in ledger.get("phases", []):
    done_count = sum(
        1 for ms in ph.get("milestones", [])
        for cb in ms.get("checkboxes", [])
        if cb.get("status") == "done"
    )
    total_count = sum(
        1 for ms in ph.get("milestones", [])
        for cb in ms.get("checkboxes", [])
    )
    
    if total_count > 0 and done_count == total_count and ph.get("status") != "complete":
        ph["status"] = "complete"
        promoted.append(ph["id"])

if promoted:
    Path("control-plane/execution-ledger.yaml").write_text(
        yaml.dump(ledger, sort_keys=False)
    )
    for pid in promoted:
        print(f"  Auto-promoted {pid} -> complete")
else:
    print("  No phases to promote")

# Count for shell
print(f"PROMOTED_COUNT={len(promoted)}")
PY

# Capture promoted count
AUTO_PROMOTED=$(python3 << 'PY'
import yaml
from pathlib import Path

ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())
promoted = []

for ph in ledger.get("phases", []):
    done_count = sum(
        1 for ms in ph.get("milestones", [])
        for cb in ms.get("checkboxes", [])
        if cb.get("status") == "done"
    )
    total_count = sum(
        1 for ms in ph.get("milestones", [])
        for cb in ms.get("checkboxes", [])
    )
    
    if total_count > 0 and done_count == total_count and ph.get("status") != "complete":
        promoted.append(ph["id"])

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
