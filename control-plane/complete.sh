#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CHECKBOX="$1"
COMMIT="${2:-$(git rev-parse --short HEAD)}"

# Run gates first
echo "Running gates..."
if ! ./control-plane/check_gates.sh; then
    echo "Gates failed - cannot complete" >&2
    exit 1
fi

python3 - "$CHECKBOX" "$COMMIT" << 'PY'
import yaml
import sys
from pathlib import Path
from datetime import datetime

checkbox = sys.argv[1]
commit = sys.argv[2]

ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())
assignments = yaml.safe_load(Path("control-plane/assignments.yaml").read_text())

# Find and update assignment
found = False
for a in assignments.get("assignments", []):
    if a["checkbox_ref"] == checkbox and a["status"] == "in_progress":
        a["status"] = "done"
        a["commit"] = commit
        a["completed_at"] = datetime.now().isoformat() + "Z"
        found = True
        break

if not found:
    print(f"ERROR: No in_progress assignment for {checkbox}", file=sys.stderr)
    sys.exit(1)

# Update ledger
for ph in ledger.get("phases", []):
    for ms in ph.get("milestones", []):
        for cb in ms.get("checkboxes", []):
            if cb["id"] == checkbox:
                cb["status"] = "done"

Path("control-plane/assignments.yaml").write_text(yaml.dump(assignments, sort_keys=False))
Path("control-plane/execution-ledger.yaml").write_text(yaml.dump(ledger, sort_keys=False))
print(f"Completed {checkbox} at commit {commit}")
PY
