import Airbender.Review.Helpers.Context.PCState.Model
import Mathlib.Tactic.NormNum

namespace Airbender.PCState.Proofs

theorem encoded_bounds {p : Nat} (hp : Arithmetic.limbBase < p) (pc : BitVec 32) :
    (encode (p := p) pc).1.val < Arithmetic.limbBase ∧
      (encode (p := p) pc).2.val < Arithmetic.limbBase := by
  have size := pc.isLt
  norm_num only [Nat.reducePow] at size
  have lo : pc.toNat % Arithmetic.limbBase < Arithmetic.limbBase :=
    Nat.mod_lt _ (by decide)
  have hi : pc.toNat / Arithmetic.limbBase < Arithmetic.limbBase := by
    dsimp [Arithmetic.limbBase] at *
    omega
  dsimp [encode]
  rw [ZMod.val_natCast_of_lt (by omega : pc.toNat % Arithmetic.limbBase < p),
    ZMod.val_natCast_of_lt (by omega : pc.toNat / Arithmetic.limbBase < p)]
  exact ⟨lo, hi⟩

end Airbender.PCState.Proofs
