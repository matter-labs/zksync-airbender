import Airbender.Proofs.Blake2Worker.NativeProcessing

namespace Airbender.Blake2Worker.Native
open Verification

/-- Logical ordinary-row processing/body acceptance derives multiplicity and
    allpadding memory laws. Physical quotient/last-row/issuance/accounting
    enforcement and initialized active-worker execution remain separate. -/
theorem local_processing_effects {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) : LocalMemoryEffects w ∧ ProcessingEffects w := by
  exact ProcessingProofs.local_effects accepted

end Airbender.Blake2Worker.Native
