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
mode = ledger.get('status_source_mode')

non_planned_phase_ids = {p['id'] for p in ledger.get('phases', []) if p.get('status') != 'planned'}
roadmap_rows = [r for r in rows if r.get('phase_id') in non_planned_phase_ids]
roadmap_status_by_id = {r['checkbox_id']: r['status'] for r in roadmap_rows}

ledger_checkbox_ids = set()
ledger_status_by_id = {}
for p in ledger.get('phases', []):
    if p.get('status') == 'planned':
        continue
    for m in p.get('milestones', []):
        for c in m.get('checkboxes', []):
            cid = c['id']
            ledger_checkbox_ids.add(cid)
            ledger_status_by_id[cid] = c.get('status')

roadmap_checkbox_ids = set(roadmap_status_by_id.keys())

missing = sorted(ledger_checkbox_ids - roadmap_checkbox_ids)
unknown = sorted(roadmap_checkbox_ids - ledger_checkbox_ids)

errors = []
if missing:
    errors.append(f"missing statuses for ledger checkbox ids: {missing}")
if unknown:
    errors.append(f"unknown roadmap checkbox ids not in ledger scope: {unknown}")

if mode == 'execution_ledger_yaml_canonical':
    mismatches = []
    for cid in sorted(ledger_checkbox_ids & roadmap_checkbox_ids):
        ls = ledger_status_by_id.get(cid)
        rs = roadmap_status_by_id.get(cid)
        if ls != rs:
            mismatches.append((cid, ls, rs))
    if mismatches:
        errors.append(f"status mismatches (ledger vs roadmap): {mismatches}")

if errors:
    print('status projection sync check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print(f'status projection sync check passed ({mode})')
PY
