#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
from pathlib import Path
import re
import yaml

root = Path('.')
ledger = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))

checkbox_id_re = re.compile(r'^[A-Z]{1,2}(\d+)\.(\d+)$')
phase_checkbox_re = re.compile(r'^- \[(x| )\]\s+P(\d+)\.(\d+)\.(\d+)\s+')

ledger_by_phase = {}
for phase in ledger.get('phases', []):
    if phase.get('status') == 'planned':
        continue
    pno = int(phase['number'])
    phase_map = {}
    for milestone in phase.get('milestones', []):
        for cb in milestone.get('checkboxes', []):
            m = checkbox_id_re.match(cb['id'])
            if not m:
                continue
            key = f"{pno}.{int(m.group(1))}.{int(m.group(2))}"
            phase_map[key] = cb.get('status') == 'done'
    ledger_by_phase[pno] = phase_map

phase_files = sorted(root.glob('PHASE*.md'))
errors = []

for pf in phase_files:
    m = re.match(r'^PHASE(\d+)\.md$', pf.name)
    if not m:
        continue
    pno = int(m.group(1))
    if pno not in ledger_by_phase:
        continue

    phase_map = {}
    for line in pf.read_text(encoding='utf-8').splitlines():
        pm = phase_checkbox_re.match(line)
        if not pm:
            continue
        fpno = int(pm.group(2))
        if fpno != pno:
            errors.append(f'{pf}: checkbox prefix P{fpno} mismatches file phase {pno}')
            continue
        key = f"{fpno}.{int(pm.group(3))}.{int(pm.group(4))}"
        phase_map[key] = pm.group(1) == 'x'

    ledger_map = ledger_by_phase[pno]
    for key, val in phase_map.items():
        if key not in ledger_map:
            errors.append(f'{pf}: missing {key} in execution-ledger')
            continue
        if ledger_map[key] != val:
            errors.append(f'{pf}: status mismatch for {key}')

    for key in sorted(ledger_map.keys()):
        if key not in phase_map:
            errors.append(f'{pf}: missing ledger checkbox {key}')

if errors:
    print('phase view sync (ledger) check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('phase view sync (ledger) check passed')
PY
