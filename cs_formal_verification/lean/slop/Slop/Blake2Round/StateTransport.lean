module
public import Slop.Delegation.NativeViews
public import Slop.Blake2Round.CallGroups

@[expose] public section

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

def wordIndex (index : Fin 40) : Fin 43 :=
  if h : index.val < 24 then ⟨1 + index.val, by omega⟩ else ⟨2 + index.val, by omega⟩

end Airbender.Blake2Round.Proofs
