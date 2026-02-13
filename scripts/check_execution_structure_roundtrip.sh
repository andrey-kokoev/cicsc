#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
import json
import subprocess
from pathlib import Path
import yaml

root = Path('.')

roadmap_struct = json.loads(
    subprocess.check_output(
        [str(root / 'control-plane/scripts/parse_roadmap_structure.py'), str(root / 'ROADMAP.md')],
        text=True,
    )
)

ledger = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))

# Only compare against phases that are non-planned in ledger (i.e. expected to exist in ROADMAP now).
ledger_non_planned = []
for p in ledger.get('phases', []):
    if p.get('status') == 'planned':
        continue
    ledger_non_planned.append({
        'id': p['id'],
        'number': p['number'],
        'title': p['title'],
        'milestones': [
            {
                'id': m['id'],
                'title': m['title'],
                'checkboxes': [{'id': c['id'], 'title': c['title']} for c in m.get('checkboxes', [])],
            }
            for m in p.get('milestones', [])
        ],
    })

roadmap_index = {(p['id'], p['number']): p for p in roadmap_struct.get('phases', [])}

errors = []
for lp in ledger_non_planned:
    key = (lp['id'], lp['number'])
    if key not in roadmap_index:
        errors.append(f"missing phase in ROADMAP: {lp['id']} Phase {lp['number']}")
        continue
    rp = roadmap_index[key]
    if rp['title'] != lp['title']:
        errors.append(
            f"phase title mismatch for {lp['id']} Phase {lp['number']}: roadmap='{rp['title']}' ledger='{lp['title']}'"
        )
        continue

    if len(rp['milestones']) != len(lp['milestones']):
        errors.append(
            f"milestone count mismatch for {lp['id']} Phase {lp['number']}: roadmap={len(rp['milestones'])} ledger={len(lp['milestones'])}"
        )
        continue

    for i, lm in enumerate(lp['milestones']):
        rm = rp['milestones'][i]
        if rm['id'] != lm['id'] or rm['title'] != lm['title']:
            errors.append(
                f"milestone mismatch in {lp['id']} Phase {lp['number']} at index {i}: roadmap=({rm['id']}, {rm['title']}) ledger=({lm['id']}, {lm['title']})"
            )
            continue
        if rm['checkboxes'] != lm['checkboxes']:
            errors.append(
                f"checkbox sequence mismatch for milestone {lm['id']}: roadmap={rm['checkboxes']} ledger={lm['checkboxes']}"
            )

if errors:
    print('execution structure roundtrip check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('execution structure roundtrip check passed')
PY
