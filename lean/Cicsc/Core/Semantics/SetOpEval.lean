import Cicsc.Core.Semantics.QueryEval

namespace Cicsc.Core

mutual
  partial def evalQuerySubsetWithSetOps (q : Query) (snaps : SnapSet) : List QueryRow :=
    evalQueryOpsWithSetOps q.pipeline (evalSourceSubset q.source snaps) snaps

  partial def evalQueryOpsWithSetOps (ops : List QueryOp) (rows : List QueryRow) (snaps : SnapSet) : List QueryRow :=
    match ops with
    | [] => rows
    | op :: rest =>
        let nextRows :=
          match op with
          | .setOp setOp rightQuery =>
              let rightRows := evalQuerySubsetWithSetOps rightQuery snaps
              applySetOp setOp rows rightRows
          | _ =>
              applyQueryOpSubset op rows
        evalQueryOpsWithSetOps rest nextRows snaps
end

theorem evalQueryOpsWithSetOps_single_setOp
  (snaps : SnapSet)
  (leftRows : List QueryRow)
  (setOp : SetOp)
  (rightQuery : Query) :
  evalQueryOpsWithSetOps [QueryOp.setOp setOp rightQuery] leftRows snaps =
    applySetOp setOp leftRows (evalQuerySubsetWithSetOps rightQuery snaps) := by
  rfl

mutual
  def supportsQueryOpWithSetOps : QueryOp → Bool
    | .setOp _ rightQuery => supportsQueryWithSetOps rightQuery
    | op => supportsQueryOpSubset op

  def supportsQueryWithSetOps (q : Query) : Bool :=
    supportsSourceSubset q.source && q.pipeline.all supportsQueryOpWithSetOps
end

end Cicsc.Core
