import Airbender.Review.JumpBranchSlt.Model
import Airbender.Proofs.JumpBranchSlt
import Mathlib.Tactic.LinearCombination

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic

/-- Selected comparison rows advance PC by four, including 32-bit wraparound.
    Alignment prevents the cleanup lookup from rounding the successor down. -/
theorem sltu_pc {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {input : Sltu.Input} {output : Airbender.Reference.RiscV.Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : Sltu.WordMapping input output w)
    (interface : Sltu.InterfaceAssumptions input output w) :
    output.pc.toBitVec = input.pc.toBitVec + 4 := by
  have bounds := local_ranges h
  have cleanup := (lookup_values hp h).2.2.2.2
  have carry := Verification.assertion_of_holds h
    ⟨21, by simp [importedConstraints, FlatOperation.constraints]⟩
  have wrap := Verification.assertion_of_holds h
    ⟨22, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry wrap
  obtain ⟨c, cb, hc⟩ := boolean_nat (x := w 39)
    (by simpa [mul_eq_zero, sub_eq_add_neg] using carry)
  obtain ⟨b, bb, hb⟩ := boolean_nat (x := w 40)
    (by simpa [mul_eq_zero, sub_eq_add_neg] using wrap)
  have branch := Verification.assertion_of_holds h
    ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, interface.otherSelectors.2.2] at branch
  have low := Verification.assertion_of_holds h
    ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨6, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, interface.selected, interface.otherSelectors.1,
    interface.otherSelectors.2.1, interface.otherSelectors.2.2, branch, hc, hb] at low high
  have initialLo : w 0 = (input.pc.lo : ZMod p) := by
    rw [mapping.pcLo]; exact (ZMod.natCast_zmod_val _).symm
  have initialHi : w 1 = (input.pc.hi : ZMod p) := by
    rw [mapping.pcHi]; exact (ZMod.natCast_zmod_val _).symm
  have lowEq : (input.pc.lo : ZMod p) + 4 = (w 36).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [initialLo] at low
    linear_combination low
  have lowNat : input.pc.lo + 4 = (w 36).val + 65536 * c :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by have := interface.initialPCLoBound; unfold limbBase at this; omega)
      (by have := bounds.2.2.2; unfold limbBase at this; omega)
      (by exact_mod_cast lowEq)
  have aligned : (w 36).val % 4 = 0 := by
    have := interface.pcAligned
    omega
  have finalLo : output.pc.lo = (w 36).val := by
    rw [mapping.finalPCLo, cleanup, aligned, Nat.sub_zero, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := bounds.2.2.2; unfold limbBase at this; omega)]
  have finalHi : w 17 = (output.pc.hi : ZMod p) := by
    rw [mapping.finalPCHi]; exact (ZMod.natCast_zmod_val _).symm
  have initialBound : input.pc.Bounded :=
    ⟨interface.initialPCLoBound, mapping.pcHi ▸ bounds.2.2.1⟩
  have finalBound : output.pc.Bounded :=
    ⟨finalLo ▸ bounds.2.2.2, interface.finalPCHiBound⟩
  have result := Word.add_of_limbs (by omega : 196608 < p)
    (left := input.pc) (right := ⟨0, 0⟩) (immediate := ⟨4, 0⟩)
    (output := output.pc) initialBound (by constructor <;> decide)
    (by constructor <;> decide) finalBound cb bb
    (by simpa [finalLo] using lowEq)
    (by
      rw [initialHi, finalHi] at high
      dsimp
      linear_combination high)
  simpa [Word.toBitVec, Word.value, limbBase] using result

end Airbender.JumpBranchSlt.Proofs
