import type { CoreIrV0 } from "../../core/ir/types"
import { installFromIr } from "./install-from-ir"

type D1Database = {
  exec (sql: string): Promise<any>
}

export async function activateVersion (params: {
  db: D1Database
  ir: CoreIrV0
  version: number
  tenant_id: string
  setActiveVersion: (tenant_id: string, version: number) => Promise<void>
}): Promise<void> {
  const { db, ir, version, tenant_id, setActiveVersion } = params
  await installFromIr({ db, ir, version })
  await setActiveVersion(tenant_id, version)
}
