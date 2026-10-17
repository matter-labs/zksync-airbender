import Airbender.Review.Helpers.Tables.Range
import Mathlib.Data.List.Perm.Basic

namespace Airbender.PCState

/-- The PC columns of a supported decoder row or a public boundary state. -/
def encode {p : Nat} (pc : BitVec 32) : ZMod p × ZMod p :=
  ((pc.toNat % Arithmetic.limbBase : Nat), (pc.toNat / Arithmetic.limbBase : Nat))

/-- The state permutation keeps both PC limbs and both timestamp columns.
    Only active execution rows belong to the lists below. -/
structure State (p : Nat) where
  pc : ZMod p × ZMod p
  timestamp : ZMod p × ZMod p

def boundary {p : Nat} (pc : BitVec 32) (timestamp : ZMod p × ZMod p) : State p :=
  ⟨encode pc, timestamp⟩

end Airbender.PCState
