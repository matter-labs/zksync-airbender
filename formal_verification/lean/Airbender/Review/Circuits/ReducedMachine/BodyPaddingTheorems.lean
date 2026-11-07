import Airbender.Proofs.ReducedMachine.NativeCSRBodyPadding

namespace Airbender.ReducedMachine.Native

/-- Complete117-equation/22-lookup runtime CSR BODY witnesses, not full physical
    rows/proofs. Original decoding/initialized callers are checked separately. -/
theorem native_csr_body_witness (active : Bool) : ∃ w : Nat → ZMod mersenne31Modulus,
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table) ∧
    w importedConstraintsTraceColumns.execute = (if active then 1 else 0) ∧
    csrRequest w = ⟨1,1991,some 0,3⟩ :=
  NativeCSRBodyPaddingProofs.complete_body active

/-- Body acceptance alone cannot justify inactive-request filtering. Actual
    full-domain decoder/auxiliary/global enforcement remains separate. -/
theorem inactive_request_filter_not_from_body : ¬ (∀ w : Nat → ZMod mersenne31Modulus,
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table) →
    w importedConstraintsTraceColumns.execute = 0 → (csrRequest w).multiplicity = 0) :=
  NativeCSRBodyPaddingProofs.no_body_filter

end Airbender.ReducedMachine.Native
