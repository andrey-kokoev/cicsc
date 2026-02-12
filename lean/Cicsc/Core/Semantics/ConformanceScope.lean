import Cicsc.Core.Syntax

namespace Cicsc.Core

def supportsVarRefV4 : VarRef → Bool
  | .state => true
  | .rowState => true
  | .row _ => true
  | .attrs _ => true
  | .input _ => true
  | .arg _ => true
  | .rowsCount => true
  | _ => false

partial def supportsExprV4 : Expr → Bool
  | .litBool _ => true
  | .litInt _ => true
  | .litString _ => true
  | .litNull => true
  | .var v => supportsVarRefV4 v
  | .not e => supportsExprV4 e
  | .and xs => xs.all supportsExprV4
  | .or xs => xs.all supportsExprV4
  | .eq a b => supportsExprV4 a && supportsExprV4 b
  | .ne a b => supportsExprV4 a && supportsExprV4 b
  | .lt a b => supportsExprV4 a && supportsExprV4 b
  | .le a b => supportsExprV4 a && supportsExprV4 b
  | .gt a b => supportsExprV4 a && supportsExprV4 b
  | .ge a b => supportsExprV4 a && supportsExprV4 b
  | .add a b => supportsExprV4 a && supportsExprV4 b
  | .sub a b => supportsExprV4 a && supportsExprV4 b
  | .mul a b => supportsExprV4 a && supportsExprV4 b
  | .div a b => supportsExprV4 a && supportsExprV4 b
  | _ => false

def supportsProjectFieldsV4 (fields : List ProjectField) : Bool :=
  fields.all (fun f => supportsExprV4 f.expr)

def supportsGroupKeysV4 (keys : List GroupKey) : Bool :=
  keys.all (fun k => supportsExprV4 k.expr)

def supportsAggExprV4 : AggExpr → Bool
  | .count => true
  | .sum e => supportsExprV4 e
  | .avg e => supportsExprV4 e
  | .min e => supportsExprV4 e
  | .max e => supportsExprV4 e
  | .stringAgg e _ => supportsExprV4 e

def supportsOrderKeysV4 (keys : List OrderKey) : Bool :=
  keys.all (fun k => supportsExprV4 k.expr)

partial def supportsSourceV4 : Source → Bool
  | .snap _ => true
  | .slaStatus _ _ => true
  | .join _ left right cond =>
      supportsSourceV4 left && supportsSourceV4 right && supportsExprV4 cond

def supportsQueryOpV4 : QueryOp → Bool
  | .filter e => supportsExprV4 e
  | .project fields => supportsProjectFieldsV4 fields
  | .groupBy keys aggs => supportsGroupKeysV4 keys && aggs.all (fun (_, a) => supportsAggExprV4 a)
  | .having e => supportsExprV4 e
  | .orderBy keys => supportsOrderKeysV4 keys
  | .limit _ => true
  | .offset _ => true
  | .setOp _ _ => false

def supportsQueryV4 (q : Query) : Bool :=
  supportsSourceV4 q.source && q.pipeline.all supportsQueryOpV4

def QueryV4Subset (q : Query) : Prop :=
  supportsQueryV4 q = true

def outOfScopeQueryOpForExecTheorem : QueryOp → Bool
  | .groupBy _ _ => true
  | .having _ => true
  | .orderBy _ => true
  | .setOp _ _ => true
  | _ => false

def outOfScopeExprForExecTheorem : Expr → Bool
  | .get _ _ => true
  | .has _ _ => true
  | .coalesce _ => true
  | .call _ _ => true
  | _ => false

theorem outOfScopeQueryOpForExecTheorem_spec (op : QueryOp) :
  outOfScopeQueryOpForExecTheorem op = true ↔
    (match op with
     | .groupBy _ _ => True
     | .having _ => True
     | .orderBy _ => True
     | .setOp _ _ => True
     | _ => False) := by
  cases op <;> simp [outOfScopeQueryOpForExecTheorem]

theorem outOfScopeExprForExecTheorem_spec (e : Expr) :
  outOfScopeExprForExecTheorem e = true ↔
    (match e with
     | .get _ _ => True
     | .has _ _ => True
     | .coalesce _ => True
     | .call _ _ => True
     | _ => False) := by
  cases e <;> simp [outOfScopeExprForExecTheorem]

end Cicsc.Core
