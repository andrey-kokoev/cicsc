import Cicsc.Core.Syntax
import Cicsc.Core.Semantics.Common

namespace Cicsc.Core

def NoReservedCollisions (ts : TypeSpec) : Prop :=
  (∀ kv ∈ ts.attrs, kv.fst ∉ ReservedRowKeys) ∧
  (∀ kv ∈ ts.shadows, kv.fst ∉ ReservedRowKeys)

end Cicsc.Core
