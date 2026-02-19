#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

# Canonical assignment/agent protocol invariants are enforced in validate.sh.
exec ./control-plane/validate.sh
