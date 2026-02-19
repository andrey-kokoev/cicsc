#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
import re
from pathlib import Path

root = Path('.')

runtime_files = []
for pattern in ('control-plane/*.sh', 'control-plane/*.py', 'control-plane/scripts/*.py'):
    runtime_files.extend(root.glob(pattern))

runtime_files = sorted(
    p for p in runtime_files
    if p.is_file()
    and p.as_posix() not in {
        'control-plane/db.py',
        'control-plane/doctor.sh',
    }
)

forbidden_symbols = {
    'create_assignment',
    'update_assignment',
    'agent_standby',
    'agent_busy',
    'set_agent_status',
}

forbidden_sql_patterns = [
    re.compile(r'INSERT\s+INTO\s+assignments', re.IGNORECASE),
    re.compile(r'UPDATE\s+assignments', re.IGNORECASE),
    re.compile(r'DELETE\s+FROM\s+assignments', re.IGNORECASE),
    re.compile(r'UPDATE\s+agents\s+SET\s+status', re.IGNORECASE),
]

errors: list[str] = []

for path in runtime_files:
    text = path.read_text(encoding='utf-8', errors='replace')
    lines = text.splitlines()

    for idx, line in enumerate(lines, start=1):
        for symbol in forbidden_symbols:
            if re.search(rf'\b{re.escape(symbol)}\b', line):
                errors.append(
                    f"{path.as_posix()}:{idx}: forbidden db mutator symbol '{symbol}'"
                )

        for pat in forbidden_sql_patterns:
            if pat.search(line):
                errors.append(
                    f"{path.as_posix()}:{idx}: forbidden direct lifecycle SQL surface '{pat.pattern}'"
                )

if errors:
    print('db protocol surface check failed')
    for err in errors:
        print(f'- {err}')
    raise SystemExit(1)

print('db protocol surface check passed')
PY
