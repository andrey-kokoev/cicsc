// /runtime/db/install-from-ir.ts

import type { CoreIrV0 } from "../../core/ir/types"
import { genSqliteSchemaFromIr } from "../../adapters/sqlite/src/schema/gen"

type D1Database = {
  exec (sql: string): Promise<any>
}

export async function installFromIr (params: {
  db: D1Database
  ir: CoreIrV0
  version: number
}): Promise<void> {
  const { db, ir, version } = params
  const { sql } = genSqliteSchemaFromIr(ir, { version })
  await db.exec(sql)
}
