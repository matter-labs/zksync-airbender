import Airbender.Proofs.AddSub.ArtifactChecks
import Airbender.Proofs.AddSub.Selectors
import Airbender.Proofs.AddSub.Arithmetic

namespace Airbender.AddSub.Proofs
open Reference.RiscV Arithmetic

theorem carry_bits {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (∃ c : Nat, c ≤ 1 ∧ w 43 = (c : ZMod p)) ∧
    (∃ d : Nat, d ≤ 1 ∧ w 33 = (d : ZMod p)) := by
  have lo := Verification.assertion_of_holds h ⟨11, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at lo hi
  constructor
  · apply Arithmetic.boolean_nat; convert lo using 1; ring
  · apply Arithmetic.boolean_nat; convert hi using 1; ring

theorem output_columns {p : Nat} [Fact p.Prime] {input : Sail.Input} {output : Sail.Output}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (zero : w 8 = if input.rd = Sail.zeroRegister then 1 else 0)
    (nonzero : input.rd ≠ Sail.zeroRegister) (m : RowWordMapping input output w) :
    w 29 = (output.destination.lo : ZMod p) ∧ w 30 = (output.destination.hi : ZMod p) := by
  have lo := Verification.assertion_of_holds h ⟨24, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨25, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    zero, nonzero] at lo hi
  rw [m.outputLo, m.outputHi, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  constructor <;> apply sub_eq_zero.mp
  · simpa only [sub_eq_add_neg] using lo
  · simpa only [sub_eq_add_neg] using hi

theorem output_bounds {p : Nat} [Fact p.Prime] {input : Sail.Input} {output : Sail.Output}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (zero : w 8 = if input.rd = Sail.zeroRegister then 1 else 0)
    (nonzero : input.rd ≠ Sail.zeroRegister) (m : RowWordMapping input output w) :
    output.destination.Bounded := by
  have lo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨0, by rw [lookup_count]; decide⟩)
  have hi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨1, by rw [lookup_count]; decide⟩)
  obtain ⟨ol, oh⟩ := output_columns h zero nonzero m
  simp [Expression.eval, Verification.environment] at lo hi
  have lp : output.destination.lo < p := by rw [m.outputLo]; exact ZMod.val_lt _
  have hp : output.destination.hi < p := by rw [m.outputHi]; exact ZMod.val_lt _
  exact ⟨by simpa only [ol, ZMod.val_natCast, Nat.mod_eq_of_lt lp] using lo,
    by simpa only [oh, ZMod.val_natCast, Nat.mod_eq_of_lt hp] using hi⟩

theorem result_word {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {input : Sail.Input} {output : Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (a : InterfaceAssumptions input output w) (nonzero : input.rd ≠ Sail.zeroRegister)
    (m : RowWordMapping input output w) :
    output.destination.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec
      | .lui => input.row.immediate.toBitVec
      | .auipc => input.row.pc.toBitVec + input.row.immediate.toBitVec := by
  obtain ⟨⟨c, cb, hc⟩, ⟨d, db, hd⟩⟩ := carry_bits h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩ := selected_bits hp h a.decoderMask
  obtain ⟨ol, oh⟩ := output_columns h a.destinationZero nonzero m
  have lo := Verification.assertion_of_holds h ⟨32, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨33, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    s0, s1, s2, s3, s4, s5, s6, s7, hc, hd, ol, oh,
    m.leftLo, m.leftHi, m.rightLo, m.rightHi, m.immediateLo, m.immediateHi,
    m.pcLo, m.pcHi] at lo hi
  apply result_of_limbs hp nonzero a.preprocessing (a.operands nonzero) a.initialPCBounds
    (output_bounds h a.destinationZero nonzero m) cb db
  cases hop : input.row.opcode
  all_goals
    have pre := a.preprocessing
    simp only [Preprocessing, nonzero, if_false, hop] at pre
    simp [hop, pre] at lo hi ⊢
    constructor <;> first | linear_combination lo | linear_combination hi

end Airbender.AddSub.Proofs
