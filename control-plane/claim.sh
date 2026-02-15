#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGENT="$1"

python3 << PY
import yaml
from pathlib import Path
from datetime import datetime

assignments = yaml.safe_load(Path("control-plane/assignments.yaml").read_text())

claimed = []
for a in assignments.get("assignments", []):
    if a["agent_ref"] == "$AGENT" and a["status"] == "open":
        a["status"] = "in_progress"
        a["started_at"] = datetime.now().isoformat() + "Z"
        claimed.append(a["checkbox_ref"])

if claimed:
    Path("control-plane/assignments.yaml").write_text(yaml.dump(assignments, sort_keys=False))
    for cb in claimed:
        print(f"Claimed {cb}")
else:
    print("No open assignments")
PY
