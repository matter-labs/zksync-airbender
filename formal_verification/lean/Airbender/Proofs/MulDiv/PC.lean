import Airbender.Proofs.MulDiv.Decoder
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Sail.PC

namespace Airbender.MulDiv.Proofs
open Reference.RiscV Arithmetic

theorem native_pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {initial final : Word} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 13).val ∧ final.hi = (w 14).val)
    (bounds : initial.Bounded) (aligned : initial.lo % 4 = 0) :
    final.Bounded ∧ final.toBitVec = initial.toBitVec + 4 := by
  have bitLo := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have bitHi := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at bitLo bitHi
  obtain ⟨c, cb, hc⟩ := Arithmetic.boolean_nat (by convert bitLo using 1; ring)
  obtain ⟨d, db, hd⟩ := Arithmetic.boolean_nat (by convert bitHi using 1; ring)
  have outLo : w 13 = (final.lo : ZMod p) := by
    rw [mapping.2.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have outHi : w 14 = (final.hi : ZMod p) := by
    rw [mapping.2.2.2]; exact (ZMod.natCast_zmod_val _).symm
  have gateLo := Verification.assertion_of_holds h ⟨37, by rw [constraint_count]; decide⟩
  have invLo := Verification.assertion_of_holds h ⟨38, by rw [constraint_count]; decide⟩
  have writeLo := Verification.assertion_of_holds h ⟨39, by rw [constraint_count]; decide⟩
  have gateHi := Verification.assertion_of_holds h ⟨40, by rw [constraint_count]; decide⟩
  have invHi := Verification.assertion_of_holds h ⟨41, by rw [constraint_count]; decide⟩
  have writeHi := Verification.assertion_of_holds h ⟨42, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    hc, hd, mapping.1, mapping.2.1, outLo, outHi] at gateLo invLo writeLo gateHi invHi writeHi
  have low : (initial.lo : ZMod p) + 4 = final.lo + 65536 * c := by
    linear_combination gateLo + writeLo
  have high : (c : ZMod p) + initial.hi = final.hi + 65536 * d := by
    linear_combination gateHi + writeHi
  have il := bounds.1; have ih := bounds.2
  unfold limbBase at il ih
  have lowBound : final.lo < 65536 := by
    interval_cases c
    · have different : initial.lo ≠ 65532 := by
        intro same
        rw [same] at invLo
        have bad : (-1 : ZMod p) = 0 := by linear_combination invLo
        norm_num at bad
      have small : initial.lo + 4 < 65536 := by omega
      have eq : (final.lo : ZMod p) = ((initial.lo + 4 : Nat) : ZMod p) := by
        push_cast; simpa using low.symm
      have valEq := congrArg ZMod.val eq
      have op : final.lo < p := by rw [mapping.2.2.1]; exact ZMod.val_lt _
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt op,
        Nat.mod_eq_of_lt (show initial.lo + 4 < p by omega)] at valEq
      omega
    · have same : initial.lo = 65532 := by
        apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega)
        linear_combination gateLo
      have zero : (final.lo : ZMod p) = 0 := by
        rw [same] at low; linear_combination -low
      have op : final.lo < p := by rw [mapping.2.2.1]; exact ZMod.val_lt _
      have valEq := congrArg ZMod.val zero
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt op, ZMod.val_zero] at valEq
      omega
  have highBound : final.hi < 65536 := by
    interval_cases d
    · have different : c + initial.hi ≠ 65536 := by
        intro same
        have eq : (c : ZMod p) + initial.hi = 65536 := by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using congrArg (fun n : Nat => (n : ZMod p)) same
        have bad : w 64 * ((c : ZMod p) + initial.hi - 65536) - 1 = 0 := by
          convert invHi using 1; ring
        simp [eq] at bad
      have small : c + initial.hi < 65536 := by omega
      have eq : (final.hi : ZMod p) = ((c + initial.hi : Nat) : ZMod p) := by
        push_cast; simpa using high.symm
      have op : final.hi < p := by rw [mapping.2.2.2]; exact ZMod.val_lt _
      have valEq := congrArg ZMod.val eq
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt op,
        Nat.mod_eq_of_lt (show c + initial.hi < p by omega)] at valEq
      omega
    · have same : c + initial.hi = 65536 := by
        apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega)
        push_cast; linear_combination gateHi
      have zero : (final.hi : ZMod p) = 0 := by
        have eq : (c : ZMod p) + initial.hi = 65536 := by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using congrArg (fun n : Nat => (n : ZMod p)) same
        linear_combination eq - high
      have op : final.hi < p := by rw [mapping.2.2.2]; exact ZMod.val_lt _
      have valEq := congrArg ZMod.val zero
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt op, ZMod.val_zero] at valEq
      omega
  have finalBounds : final.Bounded := ⟨lowBound, highBound⟩
  refine ⟨finalBounds, ?_⟩
  simpa [Word.toBitVec, Word.value] using Word.add_of_limbs hp bounds
    (right := ⟨0, 0⟩) (immediate := ⟨4, 0⟩) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    finalBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide))
    (by simpa using low) (by simpa using high)

end Airbender.MulDiv.Proofs
