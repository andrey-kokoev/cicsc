#!/usr/bin/env python3
import argparse
import re
from pathlib import Path

import yaml

PHASE_RE = re.compile(r"^## ([A-Z]{1,2})\. Phase (\d+):\s+(.+)$")
MILESTONE_RE = re.compile(r"^### ([A-Z]{1,2}\d+)\.\s+(.+)$")
CHECKBOX_RE = re.compile(r"^- \[(x| )\] ([A-Z]{1,2}\d+\.\d+)\s+(.+)$")


def parse_roadmap(md_text: str):
    phases = []
    current_phase = None
    current_milestone = None

    for line in md_text.splitlines():
        pm = PHASE_RE.match(line)
        if pm:
            current_phase = {
                "id": pm.group(1),
                "number": int(pm.group(2)),
                "title": pm.group(3).strip(),
                "status": "planned",
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
                {
                    "id": cm.group(2),
                    "title": cm.group(3).strip(),
                    "status": "done" if cm.group(1) == "x" else "open",
                }
            )

    for p in phases:
        all_boxes = [c for m in p["milestones"] for c in m["checkboxes"]]
        if not all_boxes:
            p["status"] = "planned"
            continue
        done = sum(1 for c in all_boxes if c["status"] == "done")
        if done == 0:
            p["status"] = "planned"
        elif done == len(all_boxes):
            p["status"] = "complete"
        else:
            p["status"] = "active"

    return phases


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--roadmap", default="ROADMAP.md")
    parser.add_argument("--output", default="control-plane/execution/execution-ledger.yaml")
    parser.add_argument("--mode", default="execution_ledger_yaml_canonical")
    parser.add_argument("--note", default="Execution-ledger status is canonical for roadmap phase scope.")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[2]
    roadmap_path = root / args.roadmap
    out_path = root / args.output

    phases = parse_roadmap(roadmap_path.read_text(encoding="utf-8"))

    data = {
        "version": "cicsc/execution-ledger-model-v1",
        "status_source_mode": args.mode,
        "notes": [args.note],
        "phases": phases,
    }

    out_path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=False), encoding="utf-8")
    print(f"synced execution-ledger from {args.roadmap} -> {args.output} ({len(phases)} phases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
