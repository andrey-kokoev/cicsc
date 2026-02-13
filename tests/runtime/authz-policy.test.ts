import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { isAuthorized } from "../../runtime/http/authz"

describe("runtime auth policy helpers", () => {
  it("allows operation when expected token is unset", () => {
    const req = new Request("http://localhost/any")
    assert.equal(isAuthorized(req, undefined), true)
    assert.equal(isAuthorized(req, ""), true)
  })

  it("enforces token for protected operation", () => {
    const req = new Request("http://localhost/any")
    assert.equal(isAuthorized(req, "secret"), false)
  })

  it("accepts x-cicsc-token for protected operations", () => {
    const req = new Request("http://localhost/any", { headers: { "x-cicsc-token": "secret" } })
    assert.equal(isAuthorized(req, "secret"), true)
    assert.equal(isAuthorized(req, "different"), false)
  })

  it("accepts bearer token for protected operations", () => {
    const req = new Request("http://localhost/any", {
      headers: { authorization: "Bearer migrate-secret" },
    })
    assert.equal(isAuthorized(req, "migrate-secret"), true)
    assert.equal(isAuthorized(req, "bind-secret"), false)
  })
})
