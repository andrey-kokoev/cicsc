#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
import json
import re
import subprocess
from pathlib import Path

import yaml

root = Path('.')
canonical = (root / 'control-plane/check_gates.sh').read_text(encoding='utf-8').splitlines()

# Canonical gate entrypoint must delegate to run_gate_model only.
run_gate_invocations = [l.strip() for l in canonical if re.match(r'^\./scripts/run_gate_model\.sh(\s|$)', l.strip())]
if len(run_gate_invocations) != 1:
    print('gate-model roundtrip check failed')
    print(f'- expected exactly one run_gate_model invocation, found {len(run_gate_invocations)}')
    raise SystemExit(1)

hardcoded = [l.strip() for l in canonical if re.match(r'^\./scripts/check_.*\.sh(\s|$)', l.strip())]
if hardcoded:
    print('gate-model roundtrip check failed')
    for h in hardcoded:
        print(f'- hardcoded gate script in control-plane/check_gates.sh: {h}')
    raise SystemExit(1)

# Ensure run_gate_model --print-plan matches flattened model.
model = yaml.safe_load((root / 'control-plane/gates/gate-model.yaml').read_text(encoding='utf-8'))
expected_steps = []
for gate in model.get('gates', []):
    gid = gate.get('id')
    for script in gate.get('required_scripts', []):
        expected_steps.append({'gate_id': gid, 'script': script})
        if not (root / script).exists():
            print('gate-model roundtrip check failed')
            print(f'- gate script path does not exist: {script}')
            raise SystemExit(1)

plan_run = subprocess.run(
    [str(root / 'scripts/run_gate_model.sh'), '--print-plan'],
    capture_output=True,
    text=True,
    check=False,
)
if plan_run.returncode != 0:
    print('gate-model roundtrip check failed')
    print(f"- run_gate_model --print-plan failed: {plan_run.stderr.strip() or plan_run.stdout.strip()}")
    raise SystemExit(plan_run.returncode)

order = json.loads(plan_run.stdout)
actual_steps = order.get('steps', [])
if actual_steps != expected_steps:
    print('gate-model roundtrip check failed')
    print(f'- gate plan mismatch: actual={actual_steps} expected={expected_steps}')
    raise SystemExit(1)

print('gate-model roundtrip check passed')
PY
