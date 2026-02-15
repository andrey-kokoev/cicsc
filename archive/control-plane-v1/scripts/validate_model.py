#!/usr/bin/env python3
import json
import sys
from pathlib import Path

import yaml
import jsonschema


def fmt_pos(path: Path, line: int | None = None, col: int | None = None) -> str:
    if line is None:
        return str(path)
    if col is None:
        return f"{path}:{line}"
    return f"{path}:{line}:{col}"


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: validate_model.py <model.yaml> <schema.json>", file=sys.stderr)
        return 2

    model_path = Path(sys.argv[1])
    schema_path = Path(sys.argv[2])

    if not model_path.exists():
        print(f"missing model: {model_path}", file=sys.stderr)
        return 1
    if not schema_path.exists():
        print(f"missing schema: {schema_path}", file=sys.stderr)
        return 1

    try:
        model = yaml.safe_load(model_path.read_text(encoding="utf-8"))
    except Exception as exc:
        mark = getattr(exc, "problem_mark", None)
        line = None if mark is None else int(mark.line) + 1
        col = None if mark is None else int(mark.column) + 1
        where = fmt_pos(model_path, line, col)
        print(
            f"{where}: invalid yaml: {exc}. hint: fix YAML syntax or run "
            f"'./control-plane/scripts/collab_validate.sh' for full preflight.",
            file=sys.stderr,
        )
        return 1

    try:
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
    except Exception as exc:
        line = getattr(exc, "lineno", None)
        col = getattr(exc, "colno", None)
        where = fmt_pos(schema_path, line, col)
        print(
            f"{where}: invalid json schema: {exc}. hint: repair schema JSON syntax.",
            file=sys.stderr,
        )
        return 1

    try:
        jsonschema.validate(instance=model, schema=schema)
    except jsonschema.ValidationError as exc:
        loc = ".".join(str(x) for x in exc.absolute_path)
        where = fmt_pos(model_path, 1)
        path_hint = f" path={loc}" if loc else ""
        print(
            f"{where}: schema validation failed:{path_hint} {exc.message}. hint: "
            f"check required fields/types at the reported path.",
            file=sys.stderr,
        )
        return 1

    print(f"validated {model_path} against {schema_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
