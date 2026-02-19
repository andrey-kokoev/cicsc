#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

MODE="run"
if [[ "${1:-}" == "--print-plan" ]]; then
  MODE="print"
fi

python3 - "$MODE" <<'PY'
import json
import subprocess
import sys
from pathlib import Path

import yaml

mode = sys.argv[1]
root = Path('.')
model = yaml.safe_load((root / 'control-plane/gates/gate-model.yaml').read_text(encoding='utf-8'))

steps = []
for gate in model.get('gates', []):
    gid = gate.get('id')
    for script in gate.get('required_scripts', []):
        steps.append({'gate_id': gid, 'script': script})

if not steps:
    print('gate model has no executable steps', file=sys.stderr)
    raise SystemExit(1)

if mode == 'print':
    print(json.dumps({'version': model.get('version'), 'steps': steps}, indent=2))
    raise SystemExit(0)

for step in steps:
    gate_id = step['gate_id']
    script = step['script']
    print(f"==> [{gate_id}] {script}")
    rc = subprocess.run([str(root / script)], check=False).returncode
    if rc != 0:
        print(f"gate failed: {gate_id} ({script})", file=sys.stderr)
        raise SystemExit(rc)

print('gate model execution passed')
PY
