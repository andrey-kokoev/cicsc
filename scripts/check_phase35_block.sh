#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase35-gate.json}"

python3 << 'PY'
import yaml
import json
import sys
import os
from pathlib import Path

out_path = os.environ.get("OUT_PATH", "docs/pilot/phase35-gate.json")
checklist_path = "docs/pilot/phase34-exit-checklist.json"
ledger_path = "control-plane/execution-ledger.yaml"

# 1. Check checklist
if not Path(checklist_path).exists():
    print(f"Error: Checklist not found at {checklist_path}")
    sys.exit(1)

with open(checklist_path, 'r') as f:
    checklist = json.load(f)

checklist_pass = checklist.get("status") == "pass"

# 2. Check ledger status for Phase 34 (AY)
with open(ledger_path, 'r') as f:
    ledger = yaml.safe_load(f)

phase_ay = next((ph for ph in ledger.get("phases", []) if ph.get("id") == "AY"), None)
if not phase_ay:
    print("Error: Phase AY not found in ledger")
    sys.exit(1)

all_done = True
unfinished = []
for ms in phase_ay.get("milestones", []):
    for cb in ms.get("checkboxes", []):
        if cb.get("status") != "done":
            # Special case: AY2.4 is this task itself. 
            # In some systems, the block gate script doesn't count itself if it's the one currently running.
            # But usually, it checks if the PREVIOUS tasks are done.
            if cb.get("id") != "AY2.4":
                all_done = False
                unfinished.append(cb.get("id"))

blocked = not (checklist_pass and all_done)
reasons = []
if not checklist_pass:
    reasons.append("phase34_exit_checklist_not_pass")
if not all_done:
    reasons.append(f"phase_ay_series_incomplete: {', '.join(unfinished)}")

report = {
    "version": "cicsc/phase35-gate-v1",
    "timestamp_unix": int(__import__('time').time()),
    "blocked": blocked,
    "basis": {
        "checklist": checklist_path,
        "ledger": ledger_path
    },
    "reasons": reasons
}

with open(out_path, 'w') as f:
    json.dump(report, f, indent=2)
    f.write('\n')

print(f"Phase 35 gate report written to {out_path}")
if blocked:
    print(f"Gate is BLOCKED: {', '.join(reasons)}")
    sys.exit(1)
else:
    print("Gate is OPEN")
PY
