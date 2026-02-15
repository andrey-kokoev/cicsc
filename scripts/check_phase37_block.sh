#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase37-gate.json}"

python3 << 'PY'
import yaml
import json
import sys
import os
from pathlib import Path

out_path = os.environ.get("OUT_PATH", "docs/pilot/phase37-gate.json")
checklist_path = "docs/pilot/phase36-exit-checklist.json"
ledger_path = "control-plane/execution-ledger.yaml"

# 1. Check checklist
if not Path(checklist_path).exists():
    print(f"Error: Checklist not found at {checklist_path}")
    sys.exit(1)

with open(checklist_path, 'r') as f:
    checklist = json.load(f)

checklist_pass = checklist.get("status") == "pass"

# 2. Check ledger status for Phase 36 (BA)
with open(ledger_path, 'r') as f:
    ledger = yaml.safe_load(f)

phase_ba = next((ph for ph in ledger.get("phases", []) if ph.get("id") == "BA"), None)
if not phase_ba:
    print("Error: Phase BA not found in ledger")
    sys.exit(1)

all_done = True
unfinished = []
for ms in phase_ba.get("milestones", []):
    for cb in ms.get("checkboxes", []):
        if cb.get("status") != "done":
            # Don't count BA3.3 itself if it's the one running this check (usually done by next phase)
            if cb.get("id") != "BA3.3":
                all_done = False
                unfinished.append(cb.get("id"))

blocked = not (checklist_pass and all_done)
reasons = []
if not checklist_pass:
    reasons.append("phase36_exit_checklist_not_pass")
if not all_done:
    reasons.append(f"phase_ba_series_incomplete: {', '.join(unfinished)}")

report = {
    "version": "cicsc/phase37-gate-v1",
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

print(f"Phase 37 gate report written to {out_path}")
if blocked:
    print(f"Gate is BLOCKED: {', '.join(reasons)}")
    sys.exit(1)
else:
    print("Gate is OPEN")
PY
