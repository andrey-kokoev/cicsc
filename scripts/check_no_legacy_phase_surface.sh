#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
from __future__ import annotations

import fnmatch
import re
from pathlib import Path

root = Path(".").resolve()

include_globs = [
    "scripts/**/*.sh",
    "control-plane/**/*.sh",
    "control-plane/**/*.py",
    "tests/**/*.ts",
    "cli/**/*.mjs",
    "docs/**/*.md",
    "docs/**/*.json",
    "verticals/**/*.json",
    "*.md",
    "*.json",
]

exclude_globs = [
    "**/.git/**",
    "**/node_modules/**",
    "**/dist/**",
    "**/build/**",
    "docs/pilot/**",
    "state/**",
    "tests/fixtures/**",
    "scripts/check_no_legacy_phase_surface.sh",
]

banned_patterns = [
    ("legacy_docs_pilot_ref", re.compile(r"\bdocs/pilot/")),
    ("legacy_phase_check_script_ref", re.compile(r"(?:\./)?scripts/check_phase[^\s\"'`]*\.sh")),
    ("legacy_phase_script_ref", re.compile(r"(?:\./)?scripts/phase[0-9][^\s\"'`]*\.sh")),
    ("legacy_cli_phase_suite", re.compile(r"\bphase6-concurrency\b|\bphase6-migration\b")),
]

files: set[Path] = set()
for g in include_globs:
    for p in root.glob(g):
        if not p.is_file():
            continue
        rel = p.relative_to(root).as_posix()
        if any(fnmatch.fnmatch(rel, ex) for ex in exclude_globs):
            continue
        files.add(p)

violations: list[str] = []
for p in sorted(files):
    rel = p.relative_to(root).as_posix()
    text = p.read_text(encoding="utf-8", errors="replace")
    for idx, line in enumerate(text.splitlines(), start=1):
        for name, pat in banned_patterns:
            if pat.search(line):
                violations.append(f"{rel}:{idx}: {name}: {line.strip()}")

if violations:
    print("legacy phase surface check failed")
    for v in violations:
        print(f"- {v}")
    raise SystemExit(1)

print("legacy phase surface check passed")
PY
