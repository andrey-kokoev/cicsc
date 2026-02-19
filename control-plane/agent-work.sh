#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

AGENT_ID=""
CHECKBOX=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --agent)
            AGENT_ID="${2:-}"
            shift 2
            ;;
        --checkbox)
            CHECKBOX="${2:-}"
            shift 2
            ;;
        --help|-h)
            echo "Usage: $0 --agent <AGENT_ID> --checkbox <CHECKBOX>"
            exit 0
            ;;
        *)
            echo "Unknown arg: $1" >&2
            exit 1
            ;;
    esac
done

if [[ -z "$AGENT_ID" || -z "$CHECKBOX" ]]; then
    echo "Usage: $0 --agent <AGENT_ID> --checkbox <CHECKBOX>" >&2
    exit 1
fi

# Ensure the closure commit subject always references the checkbox with a neutral label.
if git log -1 --pretty=%s | grep -Eiq "(^|[^A-Za-z0-9])${CHECKBOX}([^A-Za-z0-9]|$)"; then
    exit 0
fi

git commit --allow-empty -m "control-plane: ${CHECKBOX} close assignment" >/dev/null
