import SailRV32
import Human.ISA.RV32
import Mathlib.Tactic.IntervalCases

namespace Airbender.Reference.Sail

/-- Sail's `rev8` (a loop over the bytes) is ours. -/
theorem rev8_eq (x : BitVec 32) : SailRV32.Functions.rev8 x = RV.rev8 x := by
  simp only [SailRV32.Functions.rev8, Id.run, _root_.Sail.BitVec.length]
  rw [forIn_eq_forIn']
  simp only [ForIn'.forIn', IntRange.forIn']
  repeat (rw [IntRange.forIn'.loop]; simp [Membership.mem])
  dsimp only [pure]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [RV.rev8, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  simp only [_root_.Sail.BitVec.updateSubrange, _root_.Sail.BitVec.updateSubrange']
  interval_cases j <;> simp [_root_.Sail.BitVec.extractLsb]

end Airbender.Reference.Sail
