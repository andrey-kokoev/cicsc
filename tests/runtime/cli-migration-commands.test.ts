import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs"
import { join } from "node:path"
import { tmpdir } from "node:os"
import { spawnSync } from "node:child_process"

function setupFixture () {
  const dir = mkdtempSync(join(tmpdir(), "cicsc-cli-mig-"))
  const fromBundlePath = join(dir, "bundle.v0.json")
  const toBundlePath = join(dir, "bundle.v1.json")
  const eventsPath = join(dir, "events.v0.json")

  const from_bundle = {
    core_ir: {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new", "open"],
          initial_state: "new",
          attrs: {},
          commands: {},
          reducer: {
            ticket_created: [{ set_state: { expr: { lit: { string: "open" } } } }],
          },
        },
      },
    },
  }

  const to_bundle = {
    core_ir: {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new", "open"],
          initial_state: "new",
          attrs: {},
          commands: {},
          reducer: {
            ticket_opened: [{ set_state: { expr: { lit: { string: "open" } } } }],
            ticket_created: [{ set_state: { expr: { lit: { string: "open" } } } }],
          },
        },
      },
      migrations: {
        v0_to_v1: {
          from_version: 0,
          to_version: 1,
          on_type: "Ticket",
          event_transforms: {
            ticket_created: { emit_as: "ticket_opened" },
          },
        },
      },
    },
  }

  const events = [
    {
      tenant_id: "t",
      entity_type: "Ticket",
      entity_id: "e1",
      seq: 1,
      event_type: "ticket_created",
      payload: {},
      ts: 1,
      actor_id: "u1",
    },
  ]

  writeFileSync(fromBundlePath, JSON.stringify(from_bundle, null, 2))
  writeFileSync(toBundlePath, JSON.stringify(to_bundle, null, 2))
  writeFileSync(eventsPath, JSON.stringify(events, null, 2))

  return { dir, fromBundlePath, toBundlePath, eventsPath }
}

function runCli (args: string[]) {
  return spawnSync(process.execPath, ["cli/cicsc.mjs", ...args], {
    cwd: process.cwd(),
    encoding: "utf8",
  })
}

describe("cli migration commands", () => {
  it("runs migration-preflight and migration-dry-run", () => {
    const fx = setupFixture()
    const artifactPath = join(fx.dir, "dry-run.json")

    const preflight = runCli([
      "migration-preflight",
      "--from", fx.fromBundlePath,
      "--to", fx.toBundlePath,
      "--events", fx.eventsPath,
      "--migration", "v0_to_v1",
    ])
    assert.equal(preflight.status, 0, preflight.stderr)
    const preflightOut = JSON.parse(preflight.stdout)
    assert.equal(preflightOut.ok, true)

    const dryRun = runCli([
      "migration-dry-run",
      "--from", fx.fromBundlePath,
      "--to", fx.toBundlePath,
      "--events", fx.eventsPath,
      "--migration", "v0_to_v1",
      "--artifact", artifactPath,
    ])
    assert.equal(dryRun.status, 0, dryRun.stderr)
    const dryRunOut = JSON.parse(dryRun.stdout)
    assert.equal(dryRunOut.ok, true)

    const artifact = JSON.parse(readFileSync(artifactPath, "utf8"))
    assert.equal(artifact.version, "cicsc/migration-dry-run-v1")
    assert.equal(artifact.ok, true)
  })

  it("runs migration-rollback and writes output events", () => {
    const fx = setupFixture()
    const migratedEventsPath = join(fx.dir, "events.v1.json")
    const rolledBackPath = join(fx.dir, "events.v0.rolledback.json")

    const migratedEvents = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "e1",
        seq: 1,
        event_type: "ticket_opened",
        payload: {},
        ts: 1,
        actor_id: "u1",
      },
    ]
    writeFileSync(migratedEventsPath, JSON.stringify(migratedEvents, null, 2))

    const rollback = runCli([
      "migration-rollback",
      "--to", fx.toBundlePath,
      "--events", migratedEventsPath,
      "--migration", "v0_to_v1",
      "--out-events", rolledBackPath,
    ])
    assert.equal(rollback.status, 0, rollback.stderr)
    const rollbackOut = JSON.parse(rollback.stdout)
    assert.equal(rollbackOut.ok, true)

    const rolledBack = JSON.parse(readFileSync(rolledBackPath, "utf8"))
    assert.equal(rolledBack[0].event_type, "ticket_created")
  })
})
