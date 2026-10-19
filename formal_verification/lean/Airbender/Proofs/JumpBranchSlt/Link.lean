import Airbender.Proofs.JumpBranchSlt.Writes
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.JumpBranchSlt.Decoder

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Verification

/-- The same bits carry the saved jump link or borrow in a subtraction. -/
theorem arithmetic_carries {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c b : Nat, c ≤ 1 ∧ b ≤ 1 ∧ w 49 = (c : ZMod p) ∧ w 28 = (b : ZMod p) := by
  have carry := Verification.assertion_of_holds h
    ⟨9, by rw [constraint_count]; decide⟩
  have borrow := Verification.assertion_of_holds h
    ⟨5, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry borrow
  obtain ⟨c, cb, hc⟩ := boolean_nat (x := w 49) (by convert carry using 1; ring)
  obtain ⟨b, bb, hb⟩ := boolean_nat (x := w 28) (by convert borrow using 1; ring)
  exact ⟨c, b, cb, bb, hc, hb⟩

/-- The saved PC+4 word follows from actual carry equations and scalar ranges,
    including both limb carry and RV32 wrap. Selection is recovered separately. -/
theorem raw_jump_link {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p} {initial : Word}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 17 + w 18 = 1) (other : w 19 = 0 ∧ w 20 = 0 ∧ w 21 = 0)
    (mapping : initial.lo = (w 0).val ∧ initial.hi = (w 1).val)
    (initialBound : initial.Bounded) :
    (Word.mk (w 26).val (w 27).val).toBitVec = initial.toBitVec + 4 ∧
      (Word.mk (w 26).val (w 27).val).Bounded := by
  obtain ⟨c, b, cb, bb, hc, hb⟩ := arithmetic_carries h
  have low := assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨30, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    other.1, other.2.1, other.2.2, hc, hb] at low high
  have initialLo : w 0 = (initial.lo : ZMod p) := by
    rw [mapping.1]; exact (ZMod.natCast_zmod_val _).symm
  have initialHi : w 1 = (initial.hi : ZMod p) := by
    rw [mapping.2]; exact (ZMod.natCast_zmod_val _).symm
  have lowEq : (initial.lo : ZMod p) + 4 = (w 26).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [← initialLo]
    linear_combination low - (w 0 + 4 - w 26) * selected
  have highEq : (c : ZMod p) + initial.hi = (w 27).val + 65536 * b := by
    simp only [ZMod.natCast_zmod_val]
    rw [← initialHi]
    linear_combination high - (w 1 - w 27) * selected
  have bounds : (Word.mk (w 26).val (w 27).val).Bounded :=
    ⟨range16_bound (lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩),
     range16_bound (lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩)⟩
  have link := Word.add_of_limbs hp (left := initial) (right := ⟨0,0⟩)
    (immediate := ⟨4,0⟩) initialBound (by constructor <;> decide)
    (by constructor <;> decide) bounds (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa using lowEq) (by simpa using highEq)
  exact ⟨by simpa [Word.toBitVec, Word.value, limbBase] using link, bounds⟩

/-- The actual jump destination receives the saved PC+4 or a discarded x0 write. -/
theorem jump_link {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p} {initial : Word}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 17 + w 18 = 1) (other : w 19 = 0 ∧ w 20 = 0 ∧ w 21 = 0)
    (mapping : initial.lo = (w 0).val ∧ initial.hi = (w 1).val)
    (initialBound : initial.Bounded) (flag : w 8 = 0 ∨ w 8 = 1) :
    (Word.mk (w 38).val (w 39).val).toBitVec =
      (if w 8 = 1 then 0 else initial.toBitVec + 4) ∧
    (Word.mk (w 38).val (w 39).val).Bounded := by
  have link := raw_jump_link hp h selected other mapping initialBound
  have route := assertion_of_holds h ⟨20, by rw [constraint_count]; decide⟩
  have comparison := assertion_of_holds h ⟨21, by rw [constraint_count]; decide⟩
  have low := assertion_of_holds h ⟨22, by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨23, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    other.1, other.2.1] at route comparison low high
  have routeEq : w 36 = 1 - w 8 := by
    linear_combination -route + (1 - w 8) * selected
  have comparisonEq : w 37 = 0 := comparison
  have lowEq : w 38 = w 26 * (1 - w 8) := by
    rw [routeEq, comparisonEq] at low
    linear_combination -low
  have highEq : w 39 = w 27 * (1 - w 8) := by
    rw [routeEq] at high
    linear_combination -high
  rcases flag with zero | one
  · simp only [zero, sub_zero, mul_one] at lowEq highEq
    rw [lowEq, highEq]
    exact ⟨by simpa [zero] using link.1, link.2⟩
  · simp only [one, sub_self, mul_zero] at lowEq highEq
    simp [lowEq, highEq, one, Word.toBitVec, Word.value, Word.Bounded, limbBase]

/-- Original public decoding discharges all local selector, PC and zero-flag
    interfaces. The remaining mask condition classifies JAL/JALR rows. -/
theorem public_jump_link {w : Nat → ZMod mersenne31Modulus}
    {setup : Trace.SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w))
    (jump : (w 12).val ∈ [1,2]) :
    (Word.mk (w 38).val (w 39).val).toBitVec =
      (if (w 7).val = 0 then 0 else (Word.mk (w 0).val (w 1).val).toBitVec + 4) := by
  have inputs := decoded_inputs (by decide) image holds member
  have selectors := jump_selectors (by decide) holds jump
  have flag : w 8 = 0 ∨ w 8 = 1 := by
    rw [inputs.2.2.2]
    split_ifs <;> simp
  have result := jump_link (by decide) holds selectors.1 selectors.2
    ⟨rfl,rfl⟩ inputs.1 flag
  rw [inputs.2.2.2] at result
  by_cases zero : (w 7).val = 0
  · simpa [zero] using result.1
  · simpa [zero] using result.1

end Airbender.JumpBranchSlt.Proofs
