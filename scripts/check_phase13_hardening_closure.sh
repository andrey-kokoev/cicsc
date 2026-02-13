#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

node -e 'const fs=require("node:fs");const j=JSON.parse(fs.readFileSync("docs/pilot/phase13-hardening-closure-report.json","utf8"));process.exit(j.status==="pass"?0:1)'
