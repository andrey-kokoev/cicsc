import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import { spawnSync } from "node:child_process"

type SeedOptions = {
  checkboxStatus: "open" | "done"
  assignmentStatus: "assigned" | "done"
}

function seedLedgerDb(dbPath: string, opts: SeedOptions): void {
  const py = `
import sqlite3
import sys

db_path = sys.argv[1]
checkbox_status = sys.argv[2]
assignment_status = sys.argv[3]

conn = sqlite3.connect(db_path)
cur = conn.cursor()

cur.execute("""CREATE TABLE phases (
    id TEXT PRIMARY KEY,
    number INTEGER,
    status TEXT,
    title TEXT,
    description TEXT
)""")
cur.execute("""CREATE TABLE milestones (
    id TEXT PRIMARY KEY,
    phase_id TEXT,
    title TEXT
)""")
cur.execute("""CREATE TABLE checkboxes (
    id TEXT PRIMARY KEY,
    milestone_id TEXT,
    status TEXT,
    description TEXT
)""")
cur.execute("""CREATE TABLE assignments (
    checkbox_ref TEXT PRIMARY KEY,
    agent_ref TEXT,
    status TEXT,
    created_at TEXT,
    started_at TEXT,
    commit_sha TEXT,
    completed_at TEXT
)""")
cur.execute("""CREATE TABLE agents (
    id TEXT PRIMARY KEY,
    standby_since TEXT,
    status TEXT
)""")
cur.execute("""CREATE TABLE events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    type TEXT,
    checkbox_ref TEXT,
    agent_ref TEXT,
    timestamp TEXT,
    details TEXT
)""")

cur.execute(
    "INSERT INTO phases (id, number, status, title, description) VALUES (?, ?, ?, ?, ?)",
    ("T", 1, "in_progress", "Test Phase", ""),
)
cur.execute(
    "INSERT INTO milestones (id, phase_id, title) VALUES (?, ?, ?)",
    ("T1", "T", "Milestone T1"),
)
cur.execute(
    "INSERT INTO checkboxes (id, milestone_id, status, description) VALUES (?, ?, ?, ?)",
    ("T1.1", "T1", checkbox_status, "test checkbox"),
)
cur.execute(
    "INSERT INTO assignments (checkbox_ref, agent_ref, status, created_at) VALUES (?, ?, ?, ?)",
    ("T1.1", "AGENT_TEST", assignment_status, "2026-02-19T00:00:00Z"),
)

conn.commit()
conn.close()
`

  const run = spawnSync("python3", ["-c", py, dbPath, opts.checkboxStatus, opts.assignmentStatus], {
    cwd: process.cwd(),
    encoding: "utf8",
  })
  assert.equal(run.status, 0, run.stderr || run.stdout)
}

function runValidate(dbPath: string): ReturnType<typeof spawnSync> {
  return spawnSync("./control-plane/validate.sh", {
    cwd: process.cwd(),
    env: {
      ...process.env,
      CICSC_LEDGER_DB_PATH: dbPath,
    },
    encoding: "utf8",
  })
}

describe("control-plane assignment lifecycle invariants", () => {
  it("accepts assigned assignment with open checkbox", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-ledger-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedLedgerDb(dbPath, { checkboxStatus: "open", assignmentStatus: "assigned" })

    const run = runValidate(dbPath)
    assert.equal(run.status, 0, run.stderr || run.stdout)
  })

  it("rejects done assignment when checkbox remains open", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-ledger-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedLedgerDb(dbPath, { checkboxStatus: "open", assignmentStatus: "done" })

    const run = runValidate(dbPath)
    assert.notEqual(run.status, 0)
    assert.match(run.stderr, /assignment .* is done but checkbox is open/i)
  })

  it("rejects active assignment when checkbox is already done", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-ledger-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedLedgerDb(dbPath, { checkboxStatus: "done", assignmentStatus: "assigned" })

    const run = runValidate(dbPath)
    assert.notEqual(run.status, 0)
    assert.match(run.stderr, /done but has active assignment/i)
  })
})
