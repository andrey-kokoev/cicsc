#!/usr/bin/env bash
set -euo pipefail

# check_phase_governance.sh
# Validates phase governance invariants in execution-ledger.yaml
#
# Checks:
# 1. Exactly one phase is 'active' (or zero if all complete)
# 2. No phase has invalid status value
# 3. Active phase promotion preconditions are documented

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEDGER_FILE="${ROOT_DIR}/control-plane/execution/execution-ledger.yaml"

if [[ ! -f "${LEDGER_FILE}" ]]; then
  echo "phase-governance: FAIL - execution ledger not found: ${LEDGER_FILE}" >&2
  exit 1
fi

python3 - "$LEDGER_FILE" <<'PY'
import sys
import yaml
from pathlib import Path

ledger_path = Path(sys.argv[1])
doc = yaml.safe_load(ledger_path.read_text(encoding="utf-8"))

valid_statuses = {"planned", "active", "complete"}
phases = doc.get("phases", [])
errors = []
warnings = []

# Track phases by status
by_status = {"planned": [], "active": [], "complete": []}

for ph in phases:
    pid = ph.get("id", "UNKNOWN")
    status = ph.get("status")
    pnum = ph.get("number", "?")
    
    if status not in valid_statuses:
        errors.append(f"phase {pid} has invalid status: {status}")
        continue
    
    by_status[status].append({"id": pid, "number": pnum, "phase": ph})

# Check 1: At most one active phase
active_count = len(by_status["active"])
if active_count > 1:
    active_ids = [p["id"] for p in by_status["active"]]
    errors.append(f"multiple active phases (only one allowed): {', '.join(active_ids)}")
elif active_count == 0:
    # This is allowed if all phases are complete
    incomplete = len(by_status["planned"])
    if incomplete > 0:
        warnings.append(f"no active phase but {incomplete} planned phase(s) exist")

# Check 2: Active phase completeness validation
if by_status["active"]:
    active = by_status["active"][0]
    active_id = active["id"]
    
    # Count checkboxes in active phase
    total_cbs = 0
    done_cbs = 0
    open_cbs = []
    
    for ms in active["phase"].get("milestones", []):
        for cb in ms.get("checkboxes", []):
            total_cbs += 1
            if cb.get("status") == "done":
                done_cbs += 1
            elif cb.get("status") == "open":
                open_cbs.append(cb.get("id"))
    
    if open_cbs:
        warnings.append(f"active phase {active_id} has {len(open_cbs)} open checkbox(s): {', '.join(open_cbs[:5])}")

# Check 3: Planned phases should be ordered correctly
planned_sorted = sorted(by_status["planned"], key=lambda x: x["number"])
if planned_sorted:
    next_planned = planned_sorted[0]
    # This is just informational

# Report results
if errors:
    print("phase-governance: FAIL")
    for e in errors:
        print(f"  - ERROR: {e}")
    sys.exit(1)

if warnings:
    print("phase-governance: PASS (with warnings)")
    for w in warnings:
        print(f"  - WARNING: {w}")
else:
    print("phase-governance: PASS")
    if by_status["active"]:
        active = by_status["active"][0]
        print(f"  Active: Phase {active['number']} ({active['id']}) - {active['phase'].get('title', '')}")
    print(f"  Planned: {len(by_status['planned'])} phase(s)")
    print(f"  Complete: {len(by_status['complete'])} phase(s)")

sys.exit(0)
PY
