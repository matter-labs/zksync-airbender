module
public import Proven.Blake2Round.DiagonalG
public import Proven.Blake2Round.FinalXor
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

def wordIndex (index : Fin 40) : Fin 43 :=
  if h : index.val < 24 then ⟨1 + index.val, by omega⟩ else ⟨2 + index.val, by omega⟩

end Airbender.Blake2Round.Proofs
