# /docs/spec/auth-intrinsics-contract.md

# Auth/Role Intrinsics Contract (v0)

Runtime auth intrinsics must provide:

- `has_role(actor, role) -> boolean`
- `role_of(actor) -> string`
- `auth_ok(actor, cmdref) -> boolean`

These functions are required for policy and command authorization checks.
Implementations must fail fast at startup if this surface is missing.
