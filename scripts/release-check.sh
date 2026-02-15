#!/usr/bin/env bash
set -euo pipefail

VERSION="${1:-}"

if [[ -z "$VERSION" ]]; then
    echo "Usage: $0 <version>"
    echo "Example: $0 v1.2.0"
    exit 1
fi

# Validate version format
if ! [[ "$VERSION" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "ERROR: Invalid version format '$VERSION'"
    echo "Expected: vX.Y.Z (e.g., v1.2.0)"
    exit 1
fi

echo "=== Release Check for $VERSION ==="
echo

# Check we're on main branch
CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
if [[ "$CURRENT_BRANCH" != "main" ]]; then
    echo "ERROR: Must be on main branch (currently on $CURRENT_BRANCH)"
    exit 1
fi
echo "✅ On main branch"

# Check working tree is clean
if ! git diff --quiet; then
    echo "ERROR: Working tree has uncommitted changes"
    exit 1
fi
echo "✅ Working tree clean"

# Check version hasn't been tagged
if git rev-parse "$VERSION" >/dev/null 2>&1; then
    echo "ERROR: Version $VERSION already tagged"
    exit 1
fi
echo "✅ Version not yet tagged"

# Check semantic ordering (newer than latest)
LATEST_TAG=$(git tag -l 'v*' | sort -V | tail -1)
if [[ -n "$LATEST_TAG" && "$VERSION" < "$LATEST_TAG" ]]; then
    echo "ERROR: $VERSION is older than latest tag $LATEST_TAG"
    exit 1
fi
if [[ "$VERSION" == "$LATEST_TAG" ]]; then
    echo "ERROR: Version $VERSION already exists"
    exit 1
fi
echo "✅ Version is newer than $LATEST_TAG"

# Run validation gates
echo
echo "Running validation gates..."
./control-plane/validate.sh
echo "✅ Validation passed"

# Check all phases are complete
echo
echo "Checking phase completion..."
python3 << 'PY'
import yaml, sys
from pathlib import Path

ledger = yaml.safe_load(Path("control-plane/execution-ledger.yaml").read_text())

incomplete = []
for ph in ledger.get("phases", []):
    done = sum(1 for ms in ph["milestones"] for cb in ms["checkboxes"] if cb["status"] == "done")
    total = sum(1 for ms in ph["milestones"] for cb in ms["checkboxes"])
    if ph.get("status") != "complete" and total > 0:
        incomplete.append(f"{ph['id']}: {done}/{total}")

if incomplete:
    print("ERROR: Incomplete phases:")
    for p in incomplete:
        print(f"  - {p}")
    sys.exit(1)
else:
    print("All phases complete")
PY
echo "✅ All phases complete"

# Check CHANGELOG exists
echo
if [[ ! -f "CHANGELOG.md" ]]; then
    echo "ERROR: CHANGELOG.md not found"
    exit 1
fi

# Check CHANGELOG mentions this version
if ! grep -q "$VERSION" CHANGELOG.md; then
    echo "ERROR: $VERSION not mentioned in CHANGELOG.md"
    exit 1
fi
echo "✅ CHANGELOG.md updated"

echo
echo "==================================="
echo "✅ All release checks passed!"
echo "Ready to tag: $VERSION"
echo "==================================="
echo
echo "Next steps:"
echo "  1. git tag -a $VERSION -m 'Release $VERSION'"
echo "  2. git push origin $VERSION"
