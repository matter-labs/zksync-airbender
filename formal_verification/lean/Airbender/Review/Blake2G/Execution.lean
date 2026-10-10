import Airbender.Review.Blake2G.Model
import Airbender.Review.Delegation.Operations
import Airbender.Review.Delegation.Execution

namespace Airbender.Blake2G.Native
open Trace

/-- Inputs and outputs of the existing Clean G reference, observed from the
    native read/write ports. No expected value is supplied by these mappings. -/
def input (w : Nat → ZMod p) : Input :=
  let row : Delegation.Row p := ⟨.blakeG, w⟩
  ⟨⟨row.readWord (1 : Fin 9), row.readWord (2 : Fin 9), row.readWord (3 : Fin 9), row.readWord (4 : Fin 9)⟩,
    row.readWord (6 : Fin 9), row.readWord (7 : Fin 9)⟩

def output (w : Nat → ZMod p) : Words :=
  let row : Delegation.Row p := ⟨.blakeG, w⟩
  ⟨row.writtenWord (1 : Fin 9), row.writtenWord (2 : Fin 9), row.writtenWord (3 : Fin 9), row.writtenWord (4 : Fin 9)⟩

end Airbender.Blake2G.Native
