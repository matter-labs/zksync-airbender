import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.ReducedMachine.NativeCSRBodyPaddingProofs
open Native Verification NativeCSRPositiveWitness
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem observations (active : Bool) :
    assignment active importedConstraintsTraceColumns.execute = (if active then 1 else 0) ∧
    csrRequest (assignment active) = ⟨1,1991,some 0,3⟩ := by
  cases active <;> decide +kernel

theorem complete_body (active : Bool) : ∃ w : Nat → ZMod mersenne31Modulus,
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table) ∧
    w importedConstraintsTraceColumns.execute = (if active then 1 else 0) ∧
    csrRequest w = ⟨1,1991,some 0,3⟩ :=
  ⟨assignment active,body active,observations active⟩

/-- This proposed filter is not a consequence of the COMPLETE native BODY.
    No decoder/auxiliary/global proof acceptance or native defect is asserted. -/
theorem no_body_filter : ¬ (∀ w : Nat → ZMod mersenne31Modulus,
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table) →
    w importedConstraintsTraceColumns.execute = 0 → (csrRequest w).multiplicity = 0) := by
  intro filter
  have execute := (observations false).1
  have rejected := filter (assignment false) (body false) execute
  have request := (observations false).2
  rw [request] at rejected
  exact zero_ne_one rejected.symm

end Airbender.ReducedMachine.NativeCSRBodyPaddingProofs
