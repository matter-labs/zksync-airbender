import Airbender.Proofs.ReducedMachine.NativeComparisonFields
import Airbender.Proofs.ReducedMachine.NativeConditionalTable
import Airbender.Proofs.ReducedMachine.NativeArithmeticResult
import Airbender.Proofs.Arithmetic.Comparison

namespace Airbender.ReducedMachine.NativeComparisonResultProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual Boolean equality column; equality semantics is unnecessary for SLT,
    but the column still participates in the original accepted resolver key. -/
theorem equality_bound {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : (w 68).val ≤ 1 := by
  have e := assertion_of_holds holds ⟨21,by change 21 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e
  obtain ⟨n,bound,same⟩ := boolean_nat (by linear_combination e)
  rw [same]
  simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

/-- Internal bounded-source comparison calculation. Initialized original history
    must discharge the two source ranges before architectural execution claims. -/
theorem unsigned_borrow {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus))
    (left : (sourceWord w).Bounded) (right : (operandWord w).Bounded) :
    (w 63).val = if (sourceWord w).value < (operandWord w).value then 1 else 0 := by
  have carries := NativeArithmeticResultProofs.carries holds
  have remainder := NativeArithmeticResultProofs.scalar_bounds holds
  have equations := NativeComparisonFieldProofs.limb_equations holds useRegister mask
  have borrow := Word.borrow_iff (p := mersenne31Modulus) (by decide)
    (remainder := ⟨(w 61).val,(w 62).val⟩) (carry := (w 95).val) (borrow := (w 63).val)
    left right remainder carries.1 carries.2
    (by simpa [sourceWord,source1,operandWord,source2,importedConstraintsMemoryPorts,Trace.WordColumns.evaluate,ZMod.natCast_zmod_val] using equations.1)
    (by simpa [sourceWord,source1,operandWord,source2,importedConstraintsMemoryPorts,Trace.WordColumns.evaluate,ZMod.natCast_zmod_val] using equations.2)
  by_cases lt : (sourceWord w).value < (operandWord w).value
  · simp [lt,borrow.mpr lt]
  · have notOne := mt borrow.mp lt
    simp only [if_neg lt]
    omega

/-- Canonical packed key is derived from actual sign lookups, Boolean flags and
    original funct3. Keep field packing distinct from natural packing until here. -/
theorem key_value {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (signed : Bool) (tag : w 11 = (if signed then 2 else 3)) :
    (w 11+8*w 63+16*w 68+32*w 56+64*w 59).val =
      (if signed then 2 else 3)+8*(w 63).val+16*(w 68).val+32*(w 56).val+64*(w 59).val := by
  have signs := NativeQueryProofs.results holds
  have borrow := (NativeArithmeticResultProofs.carries holds).2
  have equal := equality_bound holds
  have s1 : (w 56).val ≤ 1 := by rw [signs.2.1]; have := signs.1; omega
  have s2 : (w 59).val ≤ 1 := by rw [signs.2.2.2.2.1]; have := signs.2.2.2.1; omega
  have bound : (if signed then 2 else 3)+8*(w 63).val+16*(w 68).val+32*(w 56).val+64*(w 59).val < mersenne31Modulus := by
    cases signed <;> simp only [Bool.false_eq_true,if_false,if_true] <;> change _ < 2147483647 <;> omega
  have cast : w 11+8*w 63+16*w 68+32*w 56+64*w 59 =
      (((if signed then 2 else 3)+8*(w 63).val+16*(w 68).val+32*(w 56).val+64*(w 59).val : Nat) : ZMod mersenne31Modulus) := by
    cases signed <;> simp [tag]
  rw [cast,ZMod.val_natCast_of_lt bound]

/-- Original comparison funct3 and actual native constraints derive no-jump and
    an exact Boolean candidate without any source range or result input. -/
theorem control {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (useRegister signed : Bool)
    (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (if signed then 2 else 3)) :
    w 66 = 0 ∧ (w 67 = 0 ∨ w 67 = 1) ∧
      w 67 = if conditionalFlag ((w 63).val+2*(w 68).val+4*(w 56).val+8*(w 59).val)
        (if signed then 2 else 3) then 1 else 0 := by
  have key := key_value holds signed tag
  have member := NativeComparisonFieldProofs.query holds useRegister mask
  have selected : (w 11+8*w 63+16*w 68+32*w 56+64*w 59).val % 8 = 2 ∨
      (w 11+8*w 63+16*w 68+32*w 56+64*w 59).val % 8 = 3 := by
    rw [key]
    cases signed <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  have resolved := NativeConditionalTableProofs.comparison member selected
  have quotient : (w 11+8*w 63+16*w 68+32*w 56+64*w 59).val / 8 =
      (w 63).val+2*(w 68).val+4*(w 56).val+8*(w 59).val := by
    rw [key]
    cases signed <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  have remainder : (w 11+8*w 63+16*w 68+32*w 56+64*w 59).val % 8 =
      if signed then 2 else 3 := by rw [key]; cases signed <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  rw [quotient,remainder] at resolved
  exact ⟨resolved.2.1,by rw [resolved.2.2]; split <;> simp,resolved.2.2⟩


/-- Exact signed/unsigned native comparison. Both internal source ranges must
    later be discharged by original initialized memory history. -/
theorem resolution {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (useRegister signed : Bool)
    (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (if signed then 2 else 3))
    (left : (sourceWord w).Bounded) (right : (operandWord w).Bounded) :
    w 67 = (((if signed then
      (if (sourceWord w).toBitVec.toInt < (operandWord w).toBitVec.toInt then 1 else 0)
      else (if (sourceWord w).value < (operandWord w).value then 1 else 0)) : Nat) : ZMod mersenne31Modulus) := by
  have borrowing := unsigned_borrow holds useRegister mask left right
  have signs := NativeQueryProofs.results holds
  have first : (w 56).val = if (sourceWord w).hi < 32768 then 0 else 1 := by
    rw [signs.2.1]
    change (w 36).val / 32768 = if (w 36).val < 32768 then 0 else 1
    have bound := signs.1
    split <;> omega
  have second : (w 59).val = if (operandWord w).hi < 32768 then 0 else 1 := by
    rw [signs.2.2.2.2.1]
    change (w 48).val / 32768 = if (w 48).val < 32768 then 0 else 1
    have bound := signs.2.2.2.1
    split <;> omega
  have actual := (control holds useRegister signed mask tag).2.2
  have eqBound := equality_bound holds
  have eqCases : (w 68).val = 0 ∨ (w 68).val = 1 := by omega
  have leftHalf : (sourceWord w).value < 2147483648 ↔ (sourceWord w).hi < 32768 := by
    have bound := left.1
    change _ < 65536 at bound
    unfold Word.value limbBase
    omega
  have rightHalf : (operandWord w).value < 2147483648 ↔ (operandWord w).hi < 32768 := by
    have bound := right.1
    change _ < 65536 at bound
    unfold Word.value limbBase
    omega
  rcases eqCases with eq | eq
  all_goals cases signed
  all_goals by_cases lp : (sourceWord w).hi < 32768 <;>
    by_cases rp : (operandWord w).hi < 32768 <;>
    by_cases lt : (sourceWord w).value < (operandWord w).value <;>
    first
    | simpa [conditionalFlag,borrowing,first,second,eq,lp,rp,lt,Word.signed_lt_iff left right] using actual
    | (exfalso; simp [lp,rp] at leftHalf rightHalf; omega)

/-- Actual candidate bounds follow from native resolver membership alone. -/
theorem candidate_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (useRegister signed : Bool)
    (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (if signed then 2 else 3)) : (candidateWord w).Bounded := by
  have candidate := NativeComparisonFieldProofs.candidate holds useRegister mask
  have bit := (control holds useRegister signed mask tag).2.1
  change (w 116).val < 65536 ∧ (w 117).val < 65536
  rw [candidate.1,candidate.2]
  rcases bit with zero | one
  · simp [zero]
  · rw [one]
    decide +kernel

/-- Comparison resolver output derives default-PC selection; it is not supplied. -/
theorem default_pc {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (useRegister signed : Bool)
    (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (if signed then 2 else 3)) : finalPC w = defaultPC w := by
  have selection := NativeComparisonFieldProofs.pc_selection holds useRegister mask
  have noJump := (control holds useRegister signed mask tag).1
  simp only [noJump,zero_mul,sub_zero,one_mul] at selection
  simp [finalPC,defaultPC,NativePortProofs.final_pc_columns,selection.1,selection.2]

/-- Assemble checked native effects with no source/value/range/result premise. -/
theorem effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (useRegister signed : Bool)
    (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (if signed then 2 else 3)) : ComparisonEffects w useRegister := by
  have resolved := control holds useRegister signed mask tag
  have written := NativeComparisonFieldProofs.write holds useRegister mask
  exact ⟨NativeComparisonFieldProofs.source holds useRegister mask,
    NativeComparisonFieldProofs.source_port holds useRegister mask,resolved.1,resolved.2.1,
    candidate_bounds holds useRegister signed mask tag,default_pc holds useRegister signed mask tag,
    written.1,written.2⟩

end Airbender.ReducedMachine.NativeComparisonResultProofs
