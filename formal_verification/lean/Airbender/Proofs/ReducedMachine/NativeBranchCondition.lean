import Airbender.Proofs.ReducedMachine.NativeBranchFields
import Airbender.Proofs.ReducedMachine.NativeBranchTable
import Airbender.Proofs.Arithmetic.Comparison

namespace Airbender.ReducedMachine.NativeBranchConditionProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Internal operand bounds must later be discharged by initialized history. -/
theorem unsigned_borrow {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (left : (sourceWord w).Bounded) (right : (operandWord w).Bounded) :
    (w 63).val = if (sourceWord w).value < (operandWord w).value then 1 else 0 := by
  have carries := NativeArithmeticResultProofs.carries holds
  have remainder := NativeArithmeticResultProofs.scalar_bounds holds
  have equations := NativeBranchFieldProofs.limb_equations holds mask
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

/-- The actual zero flag identifies full RV32 source equality, after bounded
    native subtraction. No equality answer or zero flag is supplied. -/
theorem equality {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (left : (sourceWord w).Bounded) (right : (operandWord w).Bounded) :
    w 68 = if (sourceWord w).toBitVec = (operandWord w).toBitVec then 1 else 0 := by
  have carries := NativeArithmeticResultProofs.carries holds
  have ranges := NativeArithmeticResultProofs.scalar_bounds holds
  have equations := NativeBranchFieldProofs.limb_equations holds mask
  let remainder : Word := ⟨(w 61).val,(w 62).val⟩
  have bounded : remainder.Bounded := ranges
  have subtraction := Word.sub_of_limbs (p := mersenne31Modulus) (by decide)
    (left := sourceWord w) (right := operandWord w) (output := remainder)
    (borrow := (w 95).val) (wrap := (w 63).val)
    left right bounded carries.1 carries.2
    (by simpa [sourceWord,source1,operandWord,source2,importedConstraintsMemoryPorts,
      Trace.WordColumns.evaluate,remainder,ZMod.natCast_zmod_val] using equations.1)
    (by simpa [sourceWord,source1,operandWord,source2,importedConstraintsMemoryPorts,
      Trace.WordColumns.evaluate,remainder,ZMod.natCast_zmod_val] using equations.2)
  have zero : (w 61).val = 0 ∧ (w 62).val = 0 ↔ remainder.toBitVec = 0 := by
    constructor
    · intro z
      apply BitVec.eq_of_toNat_eq
      rw [Word.toBitVec_toNat bounded]
      simp [Word.value,remainder,z.1,z.2]
    · intro z
      have value := congrArg BitVec.toNat z
      rw [Word.toBitVec_toNat bounded] at value
      change (w 61).val + 65536*(w 62).val = 0 at value
      omega
  have same : (w 61).val = 0 ∧ (w 62).val = 0 ↔
      (sourceWord w).toBitVec = (operandWord w).toBitVec := by
    rw [zero,subtraction,BitVec.sub_eq_iff_eq_add]
    simp
  simpa only [same] using NativeBranchFieldProofs.equality_flag holds mask

/-- Natural packed key is derived from actual flags/sign queries and raw tag. -/
theorem key_value {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (tag : (w 11).val < 8) :
    (w 11+8*w 63+16*w 68+32*w 56+64*w 59).val =
      (w 11).val+8*(w 63).val+16*(w 68).val+32*(w 56).val+64*(w 59).val := by
  have signs := NativeQueryProofs.results holds
  have borrow := (NativeArithmeticResultProofs.carries holds).2
  have equal := NativeComparisonResultProofs.equality_bound holds
  have s1 : (w 56).val ≤ 1 := by rw [signs.2.1]; have := signs.1; omega
  have s2 : (w 59).val ≤ 1 := by rw [signs.2.2.2.2.1]; have := signs.2.2.2.1; omega
  have bound : (w 11).val+8*(w 63).val+16*(w 68).val+32*(w 56).val+64*(w 59).val < mersenne31Modulus := by
    change _ < 2147483647
    omega
  have cast : w 11+8*w 63+16*w 68+32*w 56+64*w 59 =
      (((w 11).val+8*(w 63).val+16*(w 68).val+32*(w 56).val+64*(w 59).val : Nat) : ZMod mersenne31Modulus) := by
    simp
  rw [cast,ZMod.val_natCast_of_lt bound]

/-- All six branch tags select the native jump output. This intermediate fact
    derives Boolean control without source-range or expected-condition inputs. -/
theorem control {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (tags : (w 11).val ∈ [0,1,4,5,6,7]) :
    w 67 = 0 ∧ w 66 = if conditionalFlag
      ((w 63).val+2*(w 68).val+4*(w 56).val+8*(w 59).val) (w 11).val then 1 else 0 := by
  have tagBound : (w 11).val < 8 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at tags
    omega
  have key := key_value holds tagBound
  have remainder : (w 11+8*w 63+16*w 68+32*w 56+64*w 59).val % 8 = (w 11).val := by
    rw [key]
    omega
  have quotient : (w 11+8*w 63+16*w 68+32*w 56+64*w 59).val / 8 =
      (w 63).val+2*(w 68).val+4*(w 56).val+8*(w 59).val := by
    rw [key]
    omega
  have resolved := NativeBranchTableProofs.branch (NativeBranchFieldProofs.query holds mask)
    (by rw [remainder]; exact tags)
  rw [remainder,quotient] at resolved
  exact resolved.2

/-- Exact full RV32 branch condition. Both source ranges are internal proof
    obligations for subsequent original public initialization/history assembly. -/
theorem resolution {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (tags : (w 11).val ∈ [0,1,4,5,6,7])
    (left : (sourceWord w).Bounded) (right : (operandWord w).Bounded) :
    w 67 = 0 ∧ w 66 = if branchCondition (w 11).val (sourceWord w) (operandWord w) then 1 else 0 := by
  have borrowing := unsigned_borrow holds mask left right
  have equal := equality holds mask left right
  have equalVal : (w 68).val = if (sourceWord w).toBitVec = (operandWord w).toBitVec then 1 else 0 := by
    by_cases same : (sourceWord w).toBitVec = (operandWord w).toBitVec <;> simp [equal,same,show (1 : ZMod mersenne31Modulus).val = 1 by decide]
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
  have actual := control holds mask tags
  refine ⟨actual.1,?_⟩
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
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at tags
  rcases tags with tag | tag | tag | tag | tag | tag
  all_goals rw [tag] at actual ⊢
  all_goals by_cases eq : (sourceWord w).toBitVec = (operandWord w).toBitVec <;>
    by_cases lp : (sourceWord w).hi < 32768 <;>
    by_cases rp : (operandWord w).hi < 32768 <;>
    by_cases lt : (sourceWord w).value < (operandWord w).value <;>
    first
    | simpa [branchCondition,conditionalFlag,borrowing,equalVal,first,second,eq,lp,rp,lt,
        Word.signed_lt_iff left right] using actual.2
    | (exfalso
       have values := congrArg BitVec.toNat eq
       rw [Word.toBitVec_toNat left,Word.toBitVec_toNat right] at values
       omega)
    | (exfalso; simp [lp,rp] at leftHalf rightHalf; omega)

end Airbender.ReducedMachine.NativeBranchConditionProofs
