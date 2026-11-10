import Airbender.Proofs.Delegation.NativeViews

namespace Airbender.Blake2Round.Proofs
open Delegation.Proofs Arithmetic Reference.RiscV.Sail

def blockWords (state : State) (pointer : BitVec 32) (n offset : Nat) : Vector Word n :=
  Vector.ofFn fun i => ramEncoding state (pointer + BitVec.ofNat 32 (4 * (offset + i.val)))

end Airbender.Blake2Round.Proofs
