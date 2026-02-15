#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CHECKBOX=""
AGENT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --checkbox) CHECKBOX="$2"; shift 2 ;;
        --agent) AGENT="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

if [[ -z "$CHECKBOX" || -z "$AGENT" ]]; then
    echo "Usage: $0 --checkbox <ref> --agent <ref>"
    exit 1
fi

python3 << PY
import yaml
from pathlib import Path
from datetime import datetime

ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())
assignments = yaml.safe_load(Path("control-plane/assignments.yaml").read_text())

# Verify checkbox exists and is open
valid_checkboxes = {}
for ph in ledger.get("phases", []):
    for ms in ph.get("milestones", []):
        for cb in ms.get("checkboxes", []):
            valid_checkboxes[cb["id"]] = cb.get("status")

if "$CHECKBOX" not in valid_checkboxes:
    print(f"ERROR: Invalid checkbox: {$CHECKBOX}", file=__import__('sys').stderr)
    exit(1)

if valid_checkboxes["$CHECKBOX"] == "done":
    print(f"ERROR: Checkbox already done: {$CHECKBOX}", file=__import__('sys').stderr)
    exit(1)

# Check if already assigned
for a in assignments.get("assignments", []):
    if a["checkbox_ref"] == "$CHECKBOX" and a["status"] in ("open", "in_progress"):
        print(f"ERROR: Checkbox already assigned: {$CHECKBOX} -> {a['agent_ref']}", file=__import__('sys').stderr)
        exit(1)

# Add assignment
assignments["assignments"].append({
    "checkbox_ref": "$CHECKBOX",
    "agent_ref": "$AGENT",
    "status": "open",
    "created_at": datetime.now().isoformat() + "Z"
})

Path("control-plane/assignments.yaml").write_text(yaml.dump(assignments, sort_keys=False))
print(f"Dispatched {$CHECKBOX} -> {$AGENT}")
PY
