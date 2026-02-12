// /adapters/sqlite/src/tx.ts

export type D1Database = {
  prepare (sql: string): {
    bind (...args: any[]): any
  }
  batch (stmts: any[]): Promise<any[]>
}

export type TxCtx = {
  exec: (sql: string, binds?: any[]) => Promise<{ rows?: any[] }>
}

export async function withImmediateTx<T> (db: D1Database, fn: (tx: TxCtx) => Promise<T>): Promise<T> {
  // D1 supports batching statements; BEGIN IMMEDIATE prevents concurrent writers.
  // If any statement fails, we ROLLBACK.
  const exec = async (sql: string, binds: any[] = []) => {
    const stmt = db.prepare(sql).bind(...binds)
    const res = await db.batch([stmt])
    const r0: any = res[0] ?? {}
    if (r0?.success === false) {
      const msg = typeof r0?.error === "string" ? r0.error : `statement failed: ${sql}`
      throw new Error(msg)
    }
    // D1 returns { results } / { success } depending on API; normalize into { rows } for SELECT.
    const rows = (r0?.results ?? r0?.rows ?? undefined) as any[] | undefined
    return { rows }
  }

  await exec("BEGIN IMMEDIATE")
  try {
    const out = await fn({ exec })
    await exec("COMMIT")
    return out
  } catch (e) {
    try {
      await exec("ROLLBACK")
    } catch {
      // ignore rollback failures; original error wins
    }
    throw e
  }
}
