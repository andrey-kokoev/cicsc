#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
import json
import re
from pathlib import Path

import yaml

root = Path('.')
canonical = (root / 'scripts/check_canonical_execution_model.sh').read_text(encoding='utf-8').splitlines()

# Canonical wrapper must delegate to run_gate_model only (no duplicated hardcoded check_* calls).
run_gate_invocations = [l.strip() for l in canonical if re.match(r'^\./scripts/run_gate_model\.sh(\s|$)', l.strip())]
if len(run_gate_invocations) != 1:
    print('gate-model roundtrip check failed')
    print(f'- expected exactly one run_gate_model invocation, found {len(run_gate_invocations)}')
    raise SystemExit(1)

hardcoded = [l.strip() for l in canonical if re.match(r'^\./scripts/check_.*\.sh(\s|$)', l.strip())]
if hardcoded:
    print('gate-model roundtrip check failed')
    for h in hardcoded:
        print(f'- hardcoded gate script in canonical wrapper: {h}')
    raise SystemExit(1)

# Ensure gate-order generated view matches gate model flattening.
model = yaml.safe_load((root / 'control-plane/gates/gate-model.yaml').read_text(encoding='utf-8'))
expected_steps = []
for gate in model.get('gates', []):
    gid = gate.get('id')
    for script in gate.get('required_scripts', []):
        expected_steps.append({'gate_id': gid, 'script': script})

order_path = root / 'control-plane/views/gate-order.generated.json'
if not order_path.exists():
    print('gate-model roundtrip check failed')
    print('- missing generated gate-order file: control-plane/views/gate-order.generated.json')
    raise SystemExit(1)

order = json.loads(order_path.read_text(encoding='utf-8'))
actual_steps = order.get('steps', [])
if actual_steps != expected_steps:
    print('gate-model roundtrip check failed')
    print(f'- gate-order mismatch: actual={actual_steps} expected={expected_steps}')
    raise SystemExit(1)

print('gate-model roundtrip check passed')
PY
