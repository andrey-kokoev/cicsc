#!/usr/bin/env python3
from pathlib import Path

import yaml


def checkbox_line(status: str, cid: str, title: str) -> str:
    mark = "x" if status == "done" else " "
    return f"- [{mark}] {cid} {title}"


def render(ledger: dict) -> str:
    lines = [
        "# AUTO-GENERATED FILE. DO NOT EDIT.",
        "# Source: control-plane/execution/execution-ledger.yaml",
        "# Generator: control-plane/scripts/generate_roadmap_compat.py",
        "",
        "# ROADMAP.md (Compatibility Alias)",
        "",
        "This file is generated from `control-plane/execution/execution-ledger.yaml`.",
        "Canonical execution status truth is `control-plane/execution/execution-ledger.yaml`.",
        "",
    ]

    for phase in ledger.get("phases", []):
        lines.append(f"## {phase['id']}. Phase {phase['number']}: {phase['title']}")
        lines.append("")
        for milestone in phase.get("milestones", []):
            lines.append(f"### {milestone['id']}. {milestone['title']}")
            lines.append("")
            for checkbox in milestone.get("checkboxes", []):
                lines.append(checkbox_line(checkbox.get("status"), checkbox["id"], checkbox["title"]))
            lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    ledger_path = root / "control-plane/execution/execution-ledger.yaml"
    roadmap_path = root / "ROADMAP.md"

    ledger = yaml.safe_load(ledger_path.read_text(encoding="utf-8"))
    roadmap_path.write_text(render(ledger), encoding="utf-8")
    print("generated compatibility ROADMAP.md from execution-ledger")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
