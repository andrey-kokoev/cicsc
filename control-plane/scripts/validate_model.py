#!/usr/bin/env python3
import json
import sys
from pathlib import Path

import yaml
import jsonschema


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
        print(f"invalid yaml in {model_path}: {exc}", file=sys.stderr)
        return 1

    try:
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
    except Exception as exc:
        print(f"invalid json schema in {schema_path}: {exc}", file=sys.stderr)
        return 1

    try:
        jsonschema.validate(instance=model, schema=schema)
    except jsonschema.ValidationError as exc:
        loc = ".".join(str(x) for x in exc.absolute_path)
        where = f" at {loc}" if loc else ""
        print(f"schema validation failed for {model_path}{where}: {exc.message}", file=sys.stderr)
        return 1

    print(f"validated {model_path} against {schema_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
