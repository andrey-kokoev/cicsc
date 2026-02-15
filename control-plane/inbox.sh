#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGENT="${1:-}"

python3 << PY
import yaml
from pathlib import Path

assignments = yaml.safe_load(Path("control-plane/assignments.yaml").read_text())

agent = "$AGENT"
open_count = 0
in_progress_count = 0

for a in assignments.get("assignments", []):
    if agent and a["agent_ref"] != agent:
        continue
    status = a["status"]
    cb = a["checkbox_ref"]
    ag = a["agent_ref"]
    
    if status == "open":
        open_count += 1
        if agent:
            print(f"[OPEN] {cb}")
        else:
            print(f"[OPEN] {cb} -> {ag}")
    elif status == "in_progress":
        in_progress_count += 1
        if agent:
            print(f"[IN_PROGRESS] {cb}")
        else:
            print(f"[IN_PROGRESS] {cb} -> {ag}")

if agent:
    print(f"\nTotal: {open_count} open, {in_progress_count} in_progress")
else:
    print(f"\nTotal active: {open_count + in_progress_count}")
PY
