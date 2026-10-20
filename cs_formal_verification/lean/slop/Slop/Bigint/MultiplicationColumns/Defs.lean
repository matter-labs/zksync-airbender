import Slop.Bigint.MultiplicationRanges
import Slop.Arithmetic.Convolution
import Slop.BabyBear

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

def incoming (w : Nat → ZMod p) (i : Fin 32) : ZMod p :=
  if first : i.val = 0 then 0 else carry w ⟨i.val - 1, by have := i.isLt; omega⟩

def outgoing (w : Nat → ZMod p) (i : Fin 32) : ZMod p :=
  if last : i.val < 31 then carry w ⟨i.val, last⟩ else 0

end Airbender.Bigint.Multiplication.Proofs
