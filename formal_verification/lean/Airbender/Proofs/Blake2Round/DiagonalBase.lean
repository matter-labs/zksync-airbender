import Airbender.Proofs.Blake2Round.Mixing
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- The diagonal call consumes column outputs on lanes (k,k+5,k+10,k+15).
    Existing d bytes are reused; this accounts for its two fewer allocations. -/
def diagonalGBase {p : Nat} (call : Fin 4) (w : Nat → ZMod p) (column : Nat) : ZMod p :=
  let b := Fin.ofNat 4 (call.val + 1)
  let c := Fin.ofNat 4 (call.val + 2)
  let d := Fin.ofNat 4 (call.val + 3)
  match column with
  | 15 => columnGAssignment call w 17 | 16 => columnGAssignment call w 18
  | 19 => columnGAssignment b w 21 | 20 => columnGAssignment b w 22
  | 23 => columnGAssignment c w 25 | 24 => columnGAssignment c w 26
  | 27 => columnGAssignment d w 29 | 28 => columnGAssignment d w 30
  | 33 => w (252 + 4 * call.val) | 34 => w (253 + 4 * call.val)
  | 35 => w (254 + 4 * call.val) | 36 => w (255 + 4 * call.val)
  | 43 => columnGBase d w 72 | 46 => columnGBase d w 74
  | n => if n < 43 then w (n + 415 + 44 * call.val)
    else if n < 46 then w (n + 414 + 44 * call.val)
    else w (n + 413 + 44 * call.val)

def diagonalGAssignment {p : Nat} (call : Fin 4) (w : Nat → ZMod p) : Nat → ZMod p :=
  Blake2G.Proofs.assemble (diagonalGBase call w)

end Airbender.Blake2Round.Proofs
