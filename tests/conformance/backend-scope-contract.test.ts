import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

type ScopeContract = {
  version: string
  backend: string
  mirrors_backend?: string
  query: { supported: string[]; deferred: string[] }
  expr: { supported: string[]; deferred: string[] }
}

function readScope (fileName: string): ScopeContract {
  const p = path.resolve(process.cwd(), "tests/conformance", fileName)
  return JSON.parse(fs.readFileSync(p, "utf8")) as ScopeContract
}

function sorted (xs: string[]): string[] {
  return [...xs].sort()
}

describe("backend supported-scope contracts", () => {
  it("declares sqlite and postgres scope contracts in the same model version", () => {
    const sqlite = readScope("sqlite-supported-scope.json")
    const postgres = readScope("postgres-supported-scope.json")

    assert.equal(sqlite.version, "cicsc/backend-scope-v1")
    assert.equal(postgres.version, sqlite.version)
    assert.equal(sqlite.backend, "sqlite")
    assert.equal(postgres.backend, "postgres")
    assert.equal(postgres.mirrors_backend, "sqlite")
  })

  it("requires postgres supported/deferred operators to mirror sqlite scope model", () => {
    const sqlite = readScope("sqlite-supported-scope.json")
    const postgres = readScope("postgres-supported-scope.json")

    assert.deepEqual(sorted(postgres.query.supported), sorted(sqlite.query.supported))
    assert.deepEqual(sorted(postgres.query.deferred), sorted(sqlite.query.deferred))
    assert.deepEqual(sorted(postgres.expr.supported), sorted(sqlite.expr.supported))
    assert.deepEqual(sorted(postgres.expr.deferred), sorted(sqlite.expr.deferred))
  })
})
