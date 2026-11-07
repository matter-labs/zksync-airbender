import Airbender.Review.Circuits.ReducedMachine.Scalar16Theorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeScalar16Arguments
open Airbender.NativeScalar16Arguments Airbender.NativeScalar16ArgumentProofs
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
private abbrev csr := Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment

/-- Actual observation DATA only. Not an accepted native main/global proof. -/
noncomputable def observed : Proof F :=
  ⟨⟨⟨fun _ column => (column : F),fun _ column => (column.start : F),1⟩,
      fun _ column => (column.index : F)⟩,
    (fun _ column => if column.index = 7 then 23 else 0),fun _ column => (column.index : F),0,0⟩

theorem separate_physical_multiplicity : observed.witness 0 scalar16Layout.multiplicity = 23 ∧
    observed.initialization.main.rows 0 7 = 7 := ⟨rfl,rfl⟩

theorem actual_four_body_pairs :
    bodyPair (fun column => (column : F)) 0 = #v[61,62] ∧
    bodyPair (fun column => (column : F)) 1 = #v[69,70] ∧
    bodyPair (fun column => (column : F)) 2 = #v[90,91] ∧
    bodyPair (fun column => (column : F)) 3 = #v[122,123] := by decide +kernel

theorem actual_pair_slots : (bodyProduct 3).index = 3 ∧ (bodyAccumulator 3).start = 24 ∧
    scalar16Layout.initializationAccumulator.start = 28 ∧ scalar16Layout.tableAccumulator.start = 76 := by decide +kernel

theorem five_pairs_in_difference : pairSum observed 0 = 100 ∧ difference observed 0 = (-24 : F) := by decide +kernel

theorem all_ordinary_rows : scalar16Layout.traceLength-1 = 8388607 ∧
    65536 < scalar16Layout.traceLength-1 := by decide +kernel

/-- Complete EXISTING body plus individual original pair relations only;
    not table/sum/full auxiliary/global/worker/physical acceptance. -/
theorem complete_body_original_pairs (active : Bool) (slot : Fin 4) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (csr active))
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) ∧
    BodyPairAccepted (RingHom.id F) 1 (csr active) (fun _ => 0) (fun _ => 2) slot := by
  refine ⟨Airbender.ReducedMachine.NativeCSRPositiveWitness.body active,?_⟩
  cases active <;> fin_cases slot <;> exact ⟨by decide +kernel,by decide +kernel⟩

theorem table_scaling : tableTerm (2 : F) 3 5 7 11 = 272 := by decide +kernel

theorem all_five_difference_scaling : differenceTerm (2 : F) 23
    (fun slot => ((slot.val+1 : Nat) : F)) 7 = 12 := by decide +kernel

/-- Pure reserved-last expression slice: equality does not force each
    participating auxiliary to zero. This is not full native acceptance. -/
theorem nonzero_last_slice : differenceTerm (1 : F) 23
    (fun slot => ((slot.val+1 : Nat) : F)) 13 = 0 ∧ (23 : F) ≠ 0 := by decide +kernel

/-- PURE table slice: physical multiplicity is not a Boolean/u16/issued count. -/
theorem wide_multiplicity_slice : tableTerm (1 : F) 1 0 700000 700000 = 0 := by decide +kernel

/-- PURE pole slice; no full native proof witness or defect is asserted. -/
theorem inactive_table_pole_slice : tableTerm (1 : F) (-7) 7 0 11 = 0 := by decide +kernel

theorem nonpole_wrong_aux_rejected : tableTerm (1 : F) 1 0 0 1 ≠ 0 := by decide +kernel

theorem constant_one_difference_rejected {R : Type} [Field R] (size : Nat) (omega : R) (values : Nat → R) :
    ¬ Airbender.ReducedMachine.NativeDecoderTableArguments.DifferencePolynomialAccepted
      size omega (Polynomial.C (1 : R)) values := by
  intro accepted
  have zero := (Airbender.Delegation.SumProofs.boundary_values
    (Airbender.ReducedMachine.NativeDecoderTableArgumentProofs.as_sum accepted)).1
  exact one_ne_zero (by simpa only [Polynomial.eval_C] using zero)

theorem complete_conditional_sum {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    auxiliarySum proof true = auxiliarySum proof false := native_scalar16_auxiliary_sum embed memory pc gamma accepted

theorem complete_conditional_last {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    proof.initialization.main.auxiliary (scalar16Layout.traceLength-1) scalar16Layout.tableAccumulator =
      pairSum proof (scalar16Layout.traceLength-1) := native_scalar16_last embed memory pc gamma accepted
end Airbender.Tests.NativeScalar16Arguments
