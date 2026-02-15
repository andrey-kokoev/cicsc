#!/bin/bash
# CI script for Postgres conformance (BE3.4)

echo "Running Postgres conformance checks..."

# Run the differential tests
node --test tests/conformance/postgres-differential.test.ts

# Exit with test status
exit $?
