#!/usr/bin/env bash

emit_result() {
    local status="$1"
    local command="$2"
    local message="$3"
    shift 3

    python3 - "$status" "$command" "$message" "$@" << 'PY'
import json
import sys

status = sys.argv[1]
command = sys.argv[2]
message = sys.argv[3]
extra = {}
for item in sys.argv[4:]:
    if "=" in item:
        k, v = item.split("=", 1)
        extra[k] = v

doc = {"status": status, "command": command, "message": message}
doc.update(extra)
print(json.dumps(doc, sort_keys=True))
PY
}
