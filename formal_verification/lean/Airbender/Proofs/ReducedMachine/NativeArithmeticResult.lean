import Airbender.Proofs.ReducedMachine.NativeArithmeticFields
import Airbender.Review.Circuits.ReducedMachine.ArithmeticResult
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.ReducedMachine.NativeArithmeticResultProofs
open Verification Native Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native scalar lookups bound both actual shared arithmetic result limbs. -/
theorem scalar_bounds {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : (w 61).val < 65536 ∧ (w 62).val < 65536 := by
  have lo := range16_bound (lookup_of_holds holds ⟨0,by change 0 < 22; decide⟩)
  have hi := range16_bound (lookup_of_holds holds ⟨1,by change 1 < 22; decide⟩)
  simpa [Expression.eval,environment,limbBase] using And.intro lo hi

/-- The actual low/high carry or borrow columns are native Boolean assertions. -/
theorem carries {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : (w 95).val ≤ 1 ∧ (w 63).val ≤ 1 := by
  have e95 := assertion_of_holds holds ⟨23,by change 23 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e95
  obtain ⟨n95,b95,same95⟩ := boolean_nat (by linear_combination e95)
  have bound95 : (w 95).val ≤ 1 := by
    rw [same95]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n95 mersenne31Modulus) b95
  have e63 := assertion_of_holds holds ⟨20,by change 20 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e63
  obtain ⟨n63,b63,same63⟩ := boolean_nat (by linear_combination e63)
  have bound63 : (w 63).val ≤ 1 := by
    rw [same63]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n63 mersenne31Modulus) b63
  exact ⟨bound95,bound63⟩

/-- Internal preservation calculation. ADD/ADDI/SUB/AUIPC obtain their output
    bounds from native lookups; LUI retains the public decoder's immediate bound. -/
theorem candidate_bounds {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ArithmeticMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus))
    (immediate : mode = .lui → (arithmeticImmediateWord w).Bounded) :
    (candidateWord w).Bounded := by
  have candidate := NativeArithmeticFieldProofs.candidate holds mode mask
  have lo : w 116 = if mode = .lui then w 9 else w 61 := by
    cases mode <;> simpa [arithmeticCandidate] using
      congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) candidate
  have hi : w 117 = if mode = .lui then w 10 else w 62 := by
    cases mode <;> simpa [arithmeticCandidate] using
      congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) candidate
  have scalar := scalar_bounds holds
  cases mode <;> simp only [reduceCtorEq,if_false,if_true] at lo hi
  all_goals
    change (w 116).val < 65536 ∧ (w 117).val < 65536
    rw [lo,hi]
    first | exact scalar | exact immediate rfl

/-- Internal numerical connection only. Initialized public decoding/history must
    discharge these input bounds before exposing an architectural trace result. -/
theorem candidate_result {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ArithmeticMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus))
    (sourceBound : (sourceWord w).Bounded) (operandBound : (operandWord w).Bounded)
    (pcBound : (initialPCWord w).Bounded) (immediateBound : (arithmeticImmediateWord w).Bounded) :
    (candidateWord w).toBitVec = mode.result (sourceWord w).toBitVec (operandWord w).toBitVec
      (initialPCWord w).toBitVec (arithmeticImmediateWord w).toBitVec := by
  have candidate := NativeArithmeticFieldProofs.candidate holds mode mask
  have lo : w 116 = if mode = .lui then w 9 else w 61 := by
    cases mode <;> simpa [arithmeticCandidate] using
      congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) candidate
  have hi : w 117 = if mode = .lui then w 10 else w 62 := by
    cases mode <;> simpa [arithmeticCandidate] using
      congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) candidate
  have resultBound := candidate_bounds holds mode mask (fun _ => immediateBound)
  have cb := (carries holds).1
  have db := (carries holds).2
  have equations := NativeArithmeticFieldProofs.limb_equations holds mode mask
  have zeroBound : (⟨0,0⟩ : Word).Bounded := ⟨by decide,by decide⟩
  have sourceLo : (sourceWord w).lo = (w 35).val := rfl
  have sourceHi : (sourceWord w).hi = (w 36).val := rfl
  cases mode <;> simp only [reduceCtorEq,if_false,if_true] at lo hi
  · have e := Word.add_of_limbs (p := mersenne31Modulus) (by decide)
      (left := sourceWord w) (right := operandWord w) (immediate := ⟨0,0⟩)
      (output := candidateWord w) sourceBound operandBound zeroBound resultBound
      (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide))
      (by simpa [sourceLo,operandWord,source2,candidateWord,ZMod.natCast_zmod_val,
          Nat.cast_zero,add_zero,lo,hi] using equations.1)
      (by simpa [sourceHi,operandWord,source2,candidateWord,ZMod.natCast_zmod_val,
          Nat.cast_zero,add_zero,lo,hi] using equations.2)
    simpa [ArithmeticMode.result,Word.toBitVec,Word.value] using e
  · have e := Word.add_of_limbs (p := mersenne31Modulus) (by decide)
      (left := sourceWord w) (right := operandWord w) (immediate := ⟨0,0⟩)
      (output := candidateWord w) sourceBound operandBound zeroBound resultBound
      (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide))
      (by simpa [sourceLo,operandWord,source2,candidateWord,ZMod.natCast_zmod_val,
          Nat.cast_zero,add_zero,lo,hi] using equations.1)
      (by simpa [sourceHi,operandWord,source2,candidateWord,ZMod.natCast_zmod_val,
          Nat.cast_zero,add_zero,lo,hi] using equations.2)
    simpa [ArithmeticMode.result,Word.toBitVec,Word.value] using e
  · apply Word.sub_of_limbs (p := mersenne31Modulus) (by decide) sourceBound operandBound resultBound cb db
    · simpa [candidateWord,operandWord,source2,sourceLo,ZMod.natCast_zmod_val,lo,hi] using equations.1
    · simpa [candidateWord,operandWord,source2,sourceHi,ZMod.natCast_zmod_val,lo,hi] using equations.2
  · simp [ArithmeticMode.result,candidateWord,arithmeticImmediateWord,lo,hi]
  · have e := Word.add_of_limbs (p := mersenne31Modulus) (by decide)
      (left := initialPCWord w) (right := arithmeticImmediateWord w) (immediate := ⟨0,0⟩)
      (output := candidateWord w) pcBound immediateBound zeroBound resultBound
      (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide))
      (by simpa [initialPCWord,arithmeticImmediateWord,candidateWord,ZMod.natCast_zmod_val,
          Nat.cast_zero,add_zero,lo,hi] using equations.1)
      (by simpa [initialPCWord,arithmeticImmediateWord,candidateWord,ZMod.natCast_zmod_val,
          Nat.cast_zero,add_zero,lo,hi] using equations.2)
    simpa [ArithmeticMode.result,Word.toBitVec,Word.value] using e

end Airbender.ReducedMachine.NativeArithmeticResultProofs
