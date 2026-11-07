import Airbender.Proofs.ReducedMachine.NativeBranchPC
import Airbender.Review.Circuits.ReducedMachine.Tables.NativeBranchTheorems

namespace Tests.NativeReducedBranchResults
open Airbender Arithmetic Trace ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Every actual cleanup row is present at its native pool offset. -/
theorem actual_cleanup_rows (i : Fin 65536) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      (((jumpCleanupRow i).push 17).map Nat.cast) := by
  refine ⟨⟨i.val+262145,by change i.val+262145 < 5771521; have := i.isLt; omega⟩,?_⟩
  change _ = (NativeFixed.rowNat ⟨i.val+262145,_⟩).map Nat.cast
  have h0 : ¬ i.val+262145 < 1 := by omega
  have h1 : ¬ i.val+262145 < 65537 := by omega
  have h2 : ¬ i.val+262145 < 131073 := by omega
  have h3 : ¬ i.val+262145 < 196609 := by omega
  have h4 : ¬ i.val+262145 < 262145 := by omega
  have selected : i.val+262145 < 327681 := by have := i.isLt; omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  exact congrArg (fun v : Vector Nat 4 => v.map (Nat.cast : Nat → ZMod mersenne31Modulus))
    (NativeBranchCleanupProofs.rows i).symm

/-- Independent equality, signed and unsigned branch references at RV32 edges. -/
theorem reference_conditions :
    branchCondition 0 (Word.ofBitVec 0xffffffff) (Word.ofBitVec 0xffffffff) = true ∧
    branchCondition 1 (Word.ofBitVec 0xffffffff) (Word.ofBitVec 0xffffffff) = false ∧
    branchCondition 4 (Word.ofBitVec 0x80000000) (Word.ofBitVec 0x7fffffff) = true ∧
    branchCondition 5 (Word.ofBitVec 0x80000000) (Word.ofBitVec 0x7fffffff) = false ∧
    branchCondition 6 (Word.ofBitVec 0x80000000) (Word.ofBitVec 0x7fffffff) = false ∧
    branchCondition 7 (Word.ofBitVec 0x80000000) (Word.ofBitVec 0x7fffffff) = true := by
  decide +kernel

theorem wrong_equality_rejected {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (left : (sourceWord w).Bounded) (right : (operandWord w).Bounded)
    (same : (sourceWord w).toBitVec = (operandWord w).toBitVec) : w 68 ≠ 0 := by
  have actual := NativeBranchConditionProofs.equality native mask left right
  simp only [same,if_true] at actual
  rw [actual]
  exact one_ne_zero

theorem wrong_branch_output_rejected {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (tags : (w 11).val ∈ [0,1,4,5,6,7]) : w 67 ≠ 1 := by
  rw [(NativeBranchConditionProofs.control native mask tags).1]
  exact zero_ne_one

theorem taken_misalignment_rejected {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus))
    (misaligned : (w 69).val / 2 % 2 = 1) : w 66 ≠ 1 := by
  intro taken
  have zero := NativeBranchPCProofs.taken_bit native mask taken
  omega

theorem oversized_cleanup_rejected {bit cleaned : ZMod mersenne31Modulus} :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[65536,bit,cleaned,17] := by
  intro member
  have impossible := (NativeFixed.cleanup_implementation member).1
  have literal : (65536 : ZMod mersenne31Modulus).val = 65536 := by decide
  rw [literal] at impossible
  omega

/-- These samples check only native Boolean22/24 and target equations76/77.
    They are not complete accepted native branch rows or Sail execution. -/
private def targetRow (low high offLow offHigh carry wrap nextLow nextHigh : Nat)
    (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then low else if i = 1 then high else if i = 9 then offLow else
  if i = 10 then offHigh else if i = 23 then 1 else if i = 69 then nextLow else
  if i = 70 then nextHigh else if i = 71 then wrap else if i = 96 then carry else 0

private def targets : Vector (Nat → ZMod mersenne31Modulus) 4 :=
  #v[targetRow 0 0 8 0 0 0 8 0,targetRow 65532 0 4 0 1 0 0 1,
    targetRow 0 0 65532 65535 0 0 65532 65535,targetRow 65532 65535 8 0 1 1 4 0]

private def targetIndices : Vector (Fin 117) 4 :=
  #v[⟨22,by decide⟩,⟨24,by decide⟩,⟨76,by decide⟩,⟨77,by decide⟩]

private def targetAssertions (w : Nat → ZMod mersenne31Modulus) : Prop :=
  ∀ i : Fin 4, ((FlatOperation.constraints (importedConstraints NativeFixed.table)).get
    ⟨targetIndices[i].val,by change targetIndices[i].val < 117; exact targetIndices[i].isLt⟩).eval
      (environment w) = 0

theorem actual_target_edges (sample : Fin 4) : targetAssertions targets[sample] := by
  intro i
  fin_cases sample <;> fin_cases i <;> decide +kernel

theorem independent_target_values :
    (branchTargetWord targets[0]).toBitVec = 8 ∧
    (branchTargetWord targets[1]).toBitVec = 65536 ∧
    (branchTargetWord targets[2]).toBitVec = 0xfffffffc ∧
    (branchTargetWord targets[3]).toBitVec = 4 := by decide +kernel

end Tests.NativeReducedBranchResults
