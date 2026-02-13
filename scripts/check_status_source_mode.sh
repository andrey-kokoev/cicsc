#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
from pathlib import Path
import yaml

root = Path('.')
cfg = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))
mode = cfg.get('status_source_mode')

allowed = {'roadmap_md_canonical', 'execution_ledger_yaml_canonical'}
if mode not in allowed:
    print('status source mode check failed')
    print(f'- unsupported status_source_mode: {mode}')
    print(f'- allowed: {sorted(allowed)}')
    raise SystemExit(1)

print(f'status source mode check passed ({mode})')
PY
