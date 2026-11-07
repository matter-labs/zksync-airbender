import Airbender.Review.Circuits.Blake2Worker.Processing
import Airbender.Proofs.Blake2Worker.NativeMemory
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Worker.ProcessingProofs
open Verification Native ProcessingArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem same_source : processingSourceBytes = constraintsSourceBytes := rfl

theorem multiplicity_column : processingMultiplicity = constraintsABI.multiplicity := rfl

theorem mask_geometry : processingMaskedColumns.size = 225 ∧
    processingMemoryColumns.size = 226 ∧ processingMaskedColumns.toList.Nodup := by decide +kernel

theorem memory_partition :
    (processingMultiplicity :: processingMaskedColumns.toList).Perm processingMemoryColumns.toList := by decide +kernel

theorem access_masked (slot : Fin 43) :
    (memoryAccess slot).readTime[0] ∈ processingMaskedColumns.toList ∧
    (memoryAccess slot).readTime[1] ∈ processingMaskedColumns.toList ∧
    (memoryAccess slot).readValue[0] ∈ processingMaskedColumns.toList ∧
    (memoryAccess slot).readValue[1] ∈ processingMaskedColumns.toList ∧
    ((memoryAccess slot).writeValue.getD (memoryAccess slot).readValue)[0] ∈ processingMaskedColumns.toList ∧
    ((memoryAccess slot).writeValue.getD (memoryAccess slot).readValue)[1] ∈ processingMaskedColumns.toList := by
  fin_cases slot <;> decide +kernel

theorem unit_bit {R : Type} [CommRing R] (m : R) : processingBitTerm 1 m = m*(m-1) := by simp [processingBitTerm]

theorem unit_mask {R : Type} [CommRing R] (m value : R) : processingMaskTerm 1 m value = (m-1)*value := by simp [processingMaskTerm]

private theorem assertions_map {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (columns : List Nat)
    (expression : Nat → Expression (ZMod p)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (columns.map fun column => .assert (expression column)) ↔
      ∀ column ∈ columns, (expression column).eval (environment w) = 0 := by
  induction columns with
  | nil => simp [FlatOperation.ConstraintsHoldFlat]
  | cons column columns ih => simp [FlatOperation.ConstraintsHoldFlat,ih]

/-- Exact normalized individual source terms, not a physical quotient acceptance theorem. -/
theorem conventions_iff (w : Nat → ZMod mersenne31Modulus) :
    FlatOperation.ConstraintsHoldFlat (environment w) processingConstraints ↔
      processingBitTerm 1 (w processingMultiplicity) = 0 ∧
      ∀ column ∈ processingMaskedColumns.toList,
        processingMaskTerm 1 (w processingMultiplicity) (w column) = 0 := by
  change ((processingBitExpression.eval (environment w) = 0) ∧
    FlatOperation.ConstraintsHoldFlat (environment w)
      (processingMaskedColumns.toList.map fun column => .assert (processingMaskExpression column))) ↔ _
  rw [assertions_map]
  simp only [processingBitExpression,processingMaskExpression,Expression.eval,environment,
    processingBitTerm,processingMaskTerm,one_mul,mul_one,sub_eq_add_neg]

theorem effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) processingConstraints) : ProcessingEffects w := by
  obtain ⟨bit,masks⟩ := (conventions_iff w).mp holds
  rw [unit_bit] at bit
  have boolean : w constraintsABI.multiplicity = 0 ∨ w constraintsABI.multiplicity = 1 := by
    rw [← multiplicity_column]
    exact (mul_eq_zero.mp bit).imp id sub_eq_zero.mp
  have padding : w constraintsABI.multiplicity = 0 → ∀ column ∈ processingMaskedColumns.toList, w column = 0 := by
    intro zero column member
    have equation := masks column member
    rw [multiplicity_column,zero] at equation
    simpa [processingMaskTerm] using equation
  refine ⟨boolean,?_,?_⟩
  · intro zero column member
    have origin := memory_partition.symm.mem_iff.mp member
    rcases List.mem_cons.mp origin with same | masked
    · subst column
      simpa only [multiplicity_column] using zero
    · exact padding zero column masked
  · intro zero slot
    obtain ⟨t0,t1,r0,r1,w0,w1⟩ := access_masked slot
    exact ⟨padding zero _ t0,padding zero _ t1,padding zero _ r0,padding zero _ r1,padding zero _ w0,padding zero _ w1⟩

theorem local_effects {w : Nat → ZMod mersenne31Modulus} (accepted : LocalProcessingAccepted w) :
    LocalMemoryEffects w ∧ ProcessingEffects w :=
  ⟨MemoryProofs.local_effects accepted.body,effects accepted.conventions⟩

end Airbender.Blake2Worker.ProcessingProofs
