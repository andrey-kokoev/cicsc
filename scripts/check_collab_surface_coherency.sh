#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
from pathlib import Path

root = Path('.')
active_files = [
    Path('AGENTS.md'),
    Path('AGENTS_MAIN.md'),
    Path('AGENTS_WORKER.md'),
    Path('docs/control-plane/operator-flow.md'),
    Path('docs/guides/troubleshooting.md'),
    Path('docs/genesis/README.md'),
    Path('docs/genesis/worktree-mediated-constructive-collaboration.md'),
]

banned_refs = [
    'control-plane/collaboration/',
    'worktree-mailboxes.generated',
    '.collab-issues',
    'submit_collab_issue.sh',
    'respond_collab_issue.sh',
    'get_open_collab_issues.sh',
]

legacy_path_parts = [
    ('control-plane', 'standby.sh'),
    ('control-plane', 'main-close.sh'),
    ('control-plane', 'onboard.sh'),
    ('scripts', 'check_canonical_execution_model.sh'),
    ('scripts', 'check_status_projection_sync.sh'),
    ('scripts', 'check_execution_structure_roundtrip.sh'),
    ('scripts', 'check_execution_structure_roundtrip_ledger.sh'),
    ('control-plane', 'scripts', 'export_execution_status.py'),
    ('scripts', 'check_collaboration_model.sh'),
]
banned_refs.extend('/'.join(parts) for parts in legacy_path_parts)

errors: list[str] = []

for rel in active_files:
    if not rel.exists():
        errors.append(f"missing active collab surface file: {rel.as_posix()}")
        continue

    text = rel.read_text(encoding='utf-8', errors='replace')
    for idx, line in enumerate(text.splitlines(), start=1):
        for banned in banned_refs:
            if banned in line:
                errors.append(
                    f"{rel.as_posix()}:{idx}: banned legacy collaboration reference '{banned}'"
                )

for legacy_name in (
    'submit_collab_issue',
    'respond_collab_issue',
    'get_open_collab_issues',
):
    legacy = Path('control-plane') / f"{legacy_name}.sh"
    if legacy.exists():
        errors.append(f"legacy collaboration path must be removed: {legacy.as_posix()}")

for legacy in (Path(*parts) for parts in legacy_path_parts):
    if legacy.exists():
        errors.append(f"legacy collaboration path must be removed: {legacy.as_posix()}")

if errors:
    print('collab surface coherency check failed')
    for err in errors:
        print(f'- {err}')
    raise SystemExit(1)

print('collab surface coherency check passed')
PY
