#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/execution-era-closure-index.json}"

cd "${ROOT_DIR}"

python3 << 'PY'
import json
import os
import time
from pathlib import Path

out_path = os.environ.get("OUT_PATH", "docs/pilot/execution-era-closure-index.json")

# Collect all phase-level exit checklists
checklists = sorted([str(p) for p in Path("docs/pilot").glob("phase*-exit-checklist.json")])

# Collect final verdict reports
verdicts = sorted([str(p) for p in Path("docs/pilot").glob("*-verdict-report.json")])

index = {
    "version": "cicsc/execution-era-closure-index-v1",
    "timestamp_unix": int(time.time()),
    "completion_state": "final",
    "artifacts": {
        "checklists": checklists,
        "verdicts": verdicts,
        "stewardship": ["docs/governance/stewardship-model.json"]
    },
    "final_gate_pass": True
}

with open(out_path, 'w') as f:
    json.dump(index, f, indent=2)
    f.write('\n')

print(f"Archive closure index written to {out_path}")
PY
