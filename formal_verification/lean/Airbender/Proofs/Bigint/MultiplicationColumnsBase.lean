import Airbender.Proofs.Bigint.MultiplicationRanges
import Airbender.Proofs.Arithmetic.Convolution
import Airbender.Proofs.BabyBear

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

def incoming (w : Nat → ZMod p) (i : Fin 32) : ZMod p :=
  if first : i.val = 0 then 0 else carry w ⟨i.val - 1, by have := i.isLt; omega⟩

def outgoing (w : Nat → ZMod p) (i : Fin 32) : ZMod p :=
  if last : i.val < 31 then carry w ⟨i.val, last⟩ else 0

/-- Four adjacent columns per resource-bounded proof certificate. -/
def columnIndex (chunk : Fin 8) (lane : Fin 4) : Fin 32 :=
  ⟨4 * chunk.val + lane.val, by have := chunk.isLt; have := lane.isLt; omega⟩

end Airbender.Bigint.Multiplication.Proofs
