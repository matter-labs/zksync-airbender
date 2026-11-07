import Airbender.Review.Circuits.ReducedMachine.DecoderArguments
import Airbender.Proofs.ReducedMachine.NativeCSRBodyPadding

namespace Airbender.ReducedMachine.NativeDecoderPaddingProofs
open Native NativeDecoderArguments
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Complete actual BODY plus the individual decoder-access relation, for every
    decoder challenge. No table-sum/global/worker/physical acceptance is claimed. -/
theorem inactive_local {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R) (ch : Challenges R) :
    RowAccepted embed ch (NativeCSRPositiveWitness.assignment false) (fun _ => 0) := by
  refine ⟨NativeCSRPositiveWitness.body false,?_⟩
  have execute : NativeCSRPositiveWitness.assignment false importedConstraintsTraceColumns.execute = 0 :=
    (NativeCSRBodyPaddingProofs.observations false).1
  simp [accessTerm,execute]

theorem inactive_observations {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R) (ch : Challenges R) :
    ∃ w : Nat → ZMod mersenne31Modulus, ∃ aux : Airbender.Blake2Worker.QuarticColumn → R,
      RowAccepted embed ch w aux ∧ w importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest w = ⟨1,1991,some 0,3⟩ :=
  ⟨NativeCSRPositiveWitness.assignment false,fun _ => 0,inactive_local embed ch,
    NativeCSRBodyPaddingProofs.observations false⟩
end Airbender.ReducedMachine.NativeDecoderPaddingProofs
