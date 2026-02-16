#!/usr/bin/env bash
#==============================================================================
# deploy-postgres.sh - One-click PostgreSQL deployment
#
# Usage:
#   ./deploy-postgres.sh                           # Interactive mode
#   ./deploy-postgres.sh --connection "postgresql://..." # From connection string
#   ./deploy-postgres.sh --tenant mytenant         # Specified tenant
#   ./deploy-postgres.sh --pool 20                 # Pool size
#   ./deploy-postgres.sh --ssl                    # Enable SSL
#==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

TENANT="${CICSC_TENANT:-default}"
CONNECTION_STRING="${DATABASE_URL:-}"
POOL_SIZE="${DB_POOL_SIZE:-10}"
SSL_MODE="${DB_SSL:-disable}"

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --tenant) TENANT="$2"; shift 2 ;;
    --connection) CONNECTION_STRING="$2"; shift 2 ;;
    --pool) POOL_SIZE="$2"; shift 2 ;;
    --ssl) SSL_MODE="require"; shift ;;
    --help)
      echo "Usage: $0 [--tenant NAME] [--connection URL] [--pool N] [--ssl]"
      exit 0
      ;;
    *) shift ;;
  esac
done

echo "=== CICSC PostgreSQL Deployment ==="
echo "Tenant: $TENANT"

# BY2.2: Auto-provision via Docker or connection string
echo ""
echo "[1/4] Checking PostgreSQL..."

# Check for psql
if command -v psql &> /dev/null; then
  PSQL_VERSION=$(psql --version)
  echo "  ✓ Found: $PSQL_VERSION"
else
  echo "  ✗ psql not found"
  echo "  Install with: apt-get install postgresql-client (Debian) or brew install postgresql (macOS)"
  exit 1
fi

# If no connection string, try Docker
if [[ -z "$CONNECTION_STRING" ]]; then
  if command -v docker &> /dev/null; then
    echo "  No connection string, starting Docker container..."
    CONTAINER_NAME="cicsc-postgres-$$"
    docker run -d \
      --name "$CONTAINER_NAME" \
      -e POSTGRES_PASSWORD=cicsc \
      -e POSTGRES_DB=cicsc \
      -p 5432:5432 \
      postgres:latest || true
    CONNECTION_STRING="postgresql://postgres:cicsc@localhost:5432/cicsc"
    echo "  ✓ Started Docker container: $CONTAINER_NAME"
    echo "  Waiting for PostgreSQL to be ready..."
    sleep 3
  else
    echo "  ✗ No connection string and Docker not available"
    echo "  Provide connection string: --connection 'postgresql://user:pass@host:5432/db'"
    exit 1
  fi
fi

echo "  Connection: ${CONNECTION_STRING%@*}@***"

# BY2.3: Configure connection pooling and SSL
echo ""
echo "[2/4] Configuring connection..."

# Test connection
if ! psql "$CONNECTION_STRING" -c "SELECT 1;" --ssl-mode="$SSL_MODE" &> /dev/null; then
  echo "  ✗ Failed to connect"
  echo "  Check connection string and SSL mode"
  exit 1
fi

echo "  ✓ Connected"
echo "  Pool size: $POOL_SIZE"
echo "  SSL mode: $SSL_MODE"

# Install schema
echo ""
echo "[3/4] Installing schema..."

# Install schema using psql
psql "$CONNECTION_STRING" --ssl-mode="$SSL_MODE" -f "$ROOT/runtime/db/install-schema.sql" 2>/dev/null || {
  psql "$CONNECTION_STRING" --ssl-mode="$SSL_MODE" -c "
    CREATE TABLE IF NOT EXISTS tenant_versions (
      tenant_id TEXT PRIMARY KEY,
      active_version INTEGER NOT NULL DEFAULT 0
    );
    CREATE TABLE IF NOT EXISTS events_v0 (
      tenant_id TEXT, entity_type TEXT, entity_id TEXT,
      seq INTEGER, event_type TEXT, payload_json TEXT,
      ts BIGINT, actor_id TEXT, command_id TEXT,
      PRIMARY KEY (tenant_id, entity_type, entity_id, seq)
    );
    CREATE TABLE IF NOT EXISTS snapshots_v0 (
      tenant_id TEXT, entity_type TEXT, entity_id TEXT,
      state TEXT, attrs_json TEXT, updated_ts BIGINT,
      PRIMARY KEY (tenant_id, entity_type, entity_id)
    );
    CREATE INDEX IF NOT EXISTS idx_events_stream_v0 ON events_v0(tenant_id, entity_type, entity_id, ts);
  "
}

echo "  ✓ Schema installed"

# Initialize tenant
echo ""
echo "[4/4] Binding tenant..."
EXISTING=$(psql "$CONNECTION_STRING" --ssl-mode="$SSL_MODE" -t -c "SELECT tenant_id FROM tenant_versions WHERE tenant_id = '$TENANT';" 2>/dev/null | tr -d ' ' || echo "")
if [[ -z "$EXISTING" ]]; then
  psql "$CONNECTION_STRING" --ssl-mode="$SSL_MODE" -c "INSERT INTO tenant_versions (tenant_id, active_version) VALUES ('$TENANT', 0);"
  echo "  ✓ Created tenant: $TENANT"
else
  echo "  ✓ Tenant exists: $TENANT"
fi

# BY2.4: Print deployed URL and health check
echo ""
echo "=== Deployment Summary ==="
echo "  Connection: ${CONNECTION_STRING%@*}@***"
echo "  Tenant:     $TENANT"
echo "  Pool:       $POOL_SIZE"
echo "  SSL:        $SSL_MODE"

# Health check
echo ""
echo "=== Health Check ==="
HEALTH=$(psql "$CONNECTION_STRING" --ssl-mode="$SSL_MODE" -t -c "SELECT COUNT(*) FROM tenant_versions WHERE tenant_id = '$TENANT';" 2>/dev/null | tr -d ' ')
if [[ "$HEALTH" == "1" ]]; then
  echo "  ✓ Tenant healthy"
else
  echo "  ✗ Tenant not found"
  exit 1
fi

echo ""
echo "✓ Deployment successful!"
echo ""
echo "  Set environment:"
echo "    export DATABASE_URL='$CONNECTION_STRING'"
echo "    export DB_POOL_SIZE=$POOL_SIZE"
echo "    export DB_SSL=$SSL_MODE"
