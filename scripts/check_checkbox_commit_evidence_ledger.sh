#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
from pathlib import Path
import subprocess
import yaml

root = Path('.')
ledger = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))

errors = []
for phase in ledger.get('phases', []):
    if phase.get('status') == 'planned':
        continue
    pno = int(phase['number'])
    for milestone in phase.get('milestones', []):
        for cb in milestone.get('checkboxes', []):
            if cb.get('status') != 'done':
                continue
            cid = cb['id']
            token = f"phase{pno} {cid.lower()}"
            run = subprocess.run(
                ['git', 'log', '--all', '--regexp-ignore-case', '--grep', token, '--oneline', '-n', '1'],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
            if not run.stdout.strip():
                errors.append(
                    f'missing commit evidence for checked checkbox {cid} (expected token: "{token}")'
                )

if errors:
    print('checkbox commit evidence (ledger) check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('checkbox commit evidence (ledger) check passed')
PY
