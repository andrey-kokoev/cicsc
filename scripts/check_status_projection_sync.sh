#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./control-plane/scripts/export_roadmap_status.py ROADMAP.md > control-plane/views/roadmap-status.generated.json

python3 - <<'PY'
import json
from pathlib import Path
import yaml

root = Path('.')
status = json.loads((root / 'control-plane/views/roadmap-status.generated.json').read_text(encoding='utf-8'))
ledger = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))

rows = status.get('rows', [])

non_planned_phase_ids = {p['id'] for p in ledger.get('phases', []) if p.get('status') != 'planned'}
ledger_checkbox_ids = set()
for p in ledger.get('phases', []):
    if p.get('status') == 'planned':
        continue
    for m in p.get('milestones', []):
        for c in m.get('checkboxes', []):
            ledger_checkbox_ids.add(c['id'])

roadmap_rows = [r for r in rows if r.get('phase_id') in non_planned_phase_ids]
roadmap_checkbox_ids = {r['checkbox_id'] for r in roadmap_rows}

missing = sorted(ledger_checkbox_ids - roadmap_checkbox_ids)
unknown = sorted(roadmap_checkbox_ids - ledger_checkbox_ids)

errors = []
if missing:
    errors.append(f"missing statuses for ledger checkbox ids: {missing}")
if unknown:
    errors.append(f"unknown roadmap checkbox ids not in ledger scope: {unknown}")

if errors:
    print('status projection sync check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('status projection sync check passed')
PY
