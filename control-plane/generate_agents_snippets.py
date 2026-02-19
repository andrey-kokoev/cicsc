#!/usr/bin/env python3
"""Generate AGENTS snippet blocks from canonical operator flow doc."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "docs" / "control-plane" / "operator-flow.md"

TARGETS = [
    (ROOT / "AGENTS_MAIN.md", "main_quick_reference"),
    (ROOT / "AGENTS_WORKER.md", "worker_quick_reference"),
]


def extract_snippet(md: str, snippet_id: str) -> str:
    pattern = re.compile(
        rf"### `{re.escape(snippet_id)}`\n\n```bash\n(.*?)\n```",
        re.DOTALL,
    )
    match = pattern.search(md)
    if not match:
        raise ValueError(f"snippet not found: {snippet_id}")
    return match.group(1)


def replace_generated_block(text: str, snippet_id: str, body: str, target: Path) -> str:
    start = f"<!-- generated:{snippet_id}:start -->"
    end = f"<!-- generated:{snippet_id}:end -->"
    pattern = re.compile(rf"{re.escape(start)}.*?{re.escape(end)}", re.DOTALL)
    replacement = f"{start}\n```bash\n{body}\n```\n{end}"
    if not pattern.search(text):
        raise ValueError(
            f"generated block markers not found in {target.name} for {snippet_id}"
        )
    return pattern.sub(replacement, text, count=1)


def main() -> int:
    source_text = SOURCE.read_text(encoding="utf-8")
    for target, snippet_id in TARGETS:
        snippet = extract_snippet(source_text, snippet_id)
        original = target.read_text(encoding="utf-8")
        updated = replace_generated_block(original, snippet_id, snippet, target)
        target.write_text(updated, encoding="utf-8")
        print(f"updated {target.relative_to(ROOT)} [{snippet_id}]")
    return 0


if __name__ == "__main__":
    sys.exit(main())
