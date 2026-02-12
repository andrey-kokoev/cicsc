import type { CoreIrV0 } from "../core/ir/types"
import type { VmEnv, VmIntrinsics } from "../core/vm/eval"
import { executeCommandTx, type ExecuteTxReq, type ExecuteTxResult } from "./execute-command-tx"

export type BatchItem = ExecuteTxReq

export type BatchResult = {
  ok: boolean
  results: Array<{ ok: true; result: ExecuteTxResult } | { ok: false; error: string }>
}

export async function executeCommandBatchTx (params: {
  ir: CoreIrV0
  store: { adapter: any }
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
  requests: BatchItem[]
  continue_on_error?: boolean
  executeOne?: (p: {
    ir: CoreIrV0
    store: { adapter: any }
    intrinsics: VmIntrinsics
    policies?: VmEnv["policies"]
    req: ExecuteTxReq
  }) => Promise<ExecuteTxResult>
}): Promise<BatchResult> {
  const exec = params.executeOne ?? executeCommandTx
  const out: BatchResult["results"] = []
  let ok = true

  for (const req of params.requests) {
    try {
      const result = await exec({
        ir: params.ir,
        store: params.store,
        intrinsics: params.intrinsics,
        policies: params.policies,
        req,
      } as any)
      out.push({ ok: true, result })
    } catch (e: any) {
      ok = false
      out.push({ ok: false, error: e?.message ?? String(e) })
      if (!params.continue_on_error) break
    }
  }

  return { ok, results: out }
}
