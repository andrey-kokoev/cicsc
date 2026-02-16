#!/usr/bin/env bash
#==============================================================================
# deploy-sqlite.sh - One-click SQLite deployment
#
# Usage:
#   ./deploy-sqlite.sh                    # Interactive mode
#   ./deploy-sqlite.sh --spec path/to/spec.yaml  # From spec file
#   ./deploy-sqlite.sh --tenant mytenant         # Specified tenant
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

TENANT="${CICSC_TENANT:-default}"
SPEC_FILE=""
AUTO_CREATE="yes"

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --tenant) TENANT="$2"; shift 2 ;;
    --spec) SPEC_FILE="$2"; shift 2 ;;
    --help)
      echo "Usage: $0 [--tenant NAME] [--spec PATH]"
      exit 0
      ;;
    *) shift ;;
  esac
done

echo "=== CICSC SQLite Deployment ==="
echo "Tenant: $TENANT"

# BY1.2: Auto-detect sqlite3
echo ""
echo "[1/4] Checking sqlite3..."
if command -v sqlite3 &> /dev/null; then
  SQLITE_VERSION=$(sqlite3 --version)
  echo "  ✓ Found: $SQLITE_VERSION"
else
  echo "  ✗ sqlite3 not found"
  echo "  Install with: apt-get install sqlite3 (Debian) or brew install sqlite (macOS)"
  exit 1
fi

# BY1.1: Create deploy script
echo ""
echo "[2/4] Setting up database..."

DB_DIR="$ROOT/data"
DB_FILE="$DB_DIR/${TENANT}.db"

mkdir -p "$DB_DIR"

# Create database file
sqlite3 "$DB_FILE" "SELECT 1;" 2>/dev/null || {
  sqlite3 "$DB_FILE" ""
}

# Install schema
echo "  Installing schema..."
sqlite3 "$DB_FILE" < "$ROOT/runtime/db/install-schema.sql" 2>/dev/null || {
  # Fallback: create minimal schema if install-schema.sql doesn't exist
  sqlite3 "$DB_FILE" "
    CREATE TABLE IF NOT EXISTS tenant_versions (
      tenant_id TEXT PRIMARY KEY,
      active_version INTEGER NOT NULL DEFAULT 0
    );
    CREATE TABLE IF NOT EXISTS events_v0 (
      tenant_id TEXT, entity_type TEXT, entity_id TEXT,
      seq INTEGER, event_type TEXT, payload_json TEXT,
      ts INTEGER, actor_id TEXT, command_id TEXT,
      PRIMARY KEY (tenant_id, entity_type, entity_id, seq)
    );
    CREATE TABLE IF NOT EXISTS snapshots_v0 (
      tenant_id TEXT, entity_type TEXT, entity_id TEXT,
      state TEXT, attrs_json TEXT, updated_ts INTEGER,
      PRIMARY KEY (tenant_id, entity_type, entity_id)
    );
  "
}

echo "  ✓ Database: $DB_FILE"

# BY1.3: Initialize tenant
echo ""
echo "[3/4] Binding tenant..."
EXISTING=$(sqlite3 "$DB_FILE" "SELECT tenant_id FROM tenant_versions WHERE tenant_id = '$TENANT';" 2>/dev/null || echo "")
if [[ -z "$EXISTING" ]]; then
  sqlite3 "$DB_FILE" "INSERT INTO tenant_versions (tenant_id, active_version) VALUES ('$TENANT', 0);"
  echo "  ✓ Created tenant: $TENANT"
else
  echo "  ✓ Tenant exists: $TENANT"
fi

# BY1.4: Print URL and confirmation
echo ""
echo "[4/4] Deployment complete!"
echo ""
echo "=== Deployment Summary ==="
echo "  Database: $DB_FILE"
echo "  Tenant:   $TENANT"
echo "  Schema:   v0"
echo ""
echo "=== Next Steps ==="
echo "  Start server:"
echo "    cd $ROOT && npm run dev"
echo ""
echo "  Or use HTTP directly:"
echo "    curl -X POST http://localhost:3000/api/commands \\"
echo "      -H 'Content-Type: application/json' \\"
echo "      -d '{\"tenant_id\":\"$TENANT\",\"command\":\"Test.Command\",\"entity_id\":\"test\"}'"
echo ""
echo "✓ Deployment successful!"
