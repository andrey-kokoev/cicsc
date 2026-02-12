import Cicsc.Core.Types

namespace Cicsc.Core

abbrev ReservedRowKeys : List String := ["state"]

def mkRow (st : State) : AttrMap :=
  ("state", .vString st.st) :: (st.attrs ++ st.shadows)

end Cicsc.Core
