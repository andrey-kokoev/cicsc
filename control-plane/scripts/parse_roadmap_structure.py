#!/usr/bin/env python3
import json
import re
import sys
from pathlib import Path

PHASE_RE = re.compile(r"^## ([A-Z]{1,2})\. Phase (\d+):\s+(.+)$")
MILESTONE_RE = re.compile(r"^### ([A-Z]{1,2}\d+)\.\s+(.+)$")
CHECKBOX_RE = re.compile(r"^- \[(x| )\] ([A-Z]{1,2}\d+\.\d+)\s+(.+)$")


def parse(lines):
    phases = []
    current_phase = None
    current_milestone = None

    for line in lines:
        pm = PHASE_RE.match(line)
        if pm:
            current_phase = {
                "id": pm.group(1),
                "number": int(pm.group(2)),
                "title": pm.group(3).strip(),
                "milestones": [],
            }
            phases.append(current_phase)
            current_milestone = None
            continue

        if current_phase is None:
            continue

        mm = MILESTONE_RE.match(line)
        if mm:
            current_milestone = {
                "id": mm.group(1),
                "title": mm.group(2).strip(),
                "checkboxes": [],
            }
            current_phase["milestones"].append(current_milestone)
            continue

        cm = CHECKBOX_RE.match(line)
        if cm and current_milestone is not None:
            current_milestone["checkboxes"].append(
                {"id": cm.group(2), "title": cm.group(3).strip()}
            )

    return {"phases": phases}


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: parse_roadmap_structure.py <roadmap.md>", file=sys.stderr)
        return 2

    md_path = Path(sys.argv[1])
    if not md_path.exists():
        print(f"missing roadmap file: {md_path}", file=sys.stderr)
        return 1

    lines = md_path.read_text(encoding="utf-8").splitlines()
    out = parse(lines)
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
