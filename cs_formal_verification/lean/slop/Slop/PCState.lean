import Human.Helpers.Context.PCState.Model
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

/-- The bounded low limb excludes unsupported decoder padding. Membership then
    bounds the high limb without a separate high-limb range query. -/
theorem decoder_high_bound {p n : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {program : Vector (Option (BitVec 32)) n} {pc : ZMod p × ZMod p}
    (member : (decoderTable program).Contains #[] pc)
    (lowBound : pc.1.val < Arithmetic.limbBase) : pc.2.val < Arithmetic.limbBase := by
  change ∃ i : Fin n, pc = decoderRow program[i] at member
  obtain ⟨i, row⟩ := member
  cases entry : program[i] with
  | none =>
    have low : pc.1 = -1 := by simpa [decoderRow, entry] using congrArg Prod.fst row
    have sentinel : (-1 : ZMod p).val = p - 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by
        dsimp [Arithmetic.limbBase] at hp
        omega : p ≠ 0)
      exact ZMod.val_neg_one k
    rw [low, sentinel] at lowBound
    dsimp [Arithmetic.limbBase] at hp lowBound
    omega
  | some address =>
    have high : pc.2 = (encode address).2 := by
      simpa [decoderRow, entry] using congrArg Prod.snd row
    rw [high]
    exact (encoded_bounds hp address).2

/-- Membership transfer needs no temporal-order theorem: every outgoing tuple
    matches either a decoder input or the bounded terminal boundary. -/
theorem outgoing_bounds {p n : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {context : Context p n} (interface : Interface context) {pc : ZMod p × ZMod p}
    (outgoing : Outgoing context pc) (lowBound : pc.1.val < Arithmetic.limbBase) :
    pc.1.val < Arithmetic.limbBase ∧ pc.2.val < Arithmetic.limbBase := by
  obtain ⟨state, outgoing, rfl⟩ := outgoing
  have matched := interface.balanced.mem_iff.mp (List.mem_cons_of_mem _ outgoing)
  rcases List.mem_cons.mp matched with terminal | incoming
  · subst state
    exact encoded_bounds hp context.terminalPC
  · exact ⟨lowBound, decoder_high_bound hp (interface.decoded _ incoming) lowBound⟩

end Airbender.PCState.Proofs
