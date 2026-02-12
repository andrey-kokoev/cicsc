import { DatabaseSync } from "node:sqlite"

export function makeSqliteFileD1 (dbPath) {
  const db = new DatabaseSync(dbPath)
  db.exec("PRAGMA journal_mode = WAL;")
  db.exec("PRAGMA foreign_keys = ON;")

  return {
    exec (sql) {
      db.exec(sql)
      return Promise.resolve({ ok: true })
    },

    prepare (sql) {
      return {
        bind (...values) {
          return makePrepared(db, sql, values)
        },
      }
    },

    async batch (stmts) {
      const out = []
      for (const s of stmts) {
        const run = typeof s?._runBound === "function" ? s._runBound : null
        if (!run) {
          out.push({ success: false, error: "invalid prepared statement object", results: [] })
          continue
        }
        try {
          const r = run()
          out.push({ success: true, results: r.results ?? [] })
        } catch (e) {
          out.push({ success: false, error: e?.message ?? String(e), results: [] })
        }
      }
      return out
    },
  }
}

function makePrepared (db, sql, values) {
  const stmt = db.prepare(sql)

  const runBound = () => {
    const upper = sql.trimStart().toUpperCase()
    if (upper.startsWith("SELECT")) {
      return { results: stmt.all(...values) ?? [] }
    }
    stmt.run(...values)
    return { results: [] }
  }

  return {
    sql,
    args: values,
    _runBound: runBound,
    async run () {
      runBound()
      return { success: true }
    },
    async first () {
      const rows = stmt.all(...values) ?? []
      return rows.length > 0 ? rows[0] : null
    },
    async all () {
      return { results: stmt.all(...values) ?? [] }
    },
  }
}
