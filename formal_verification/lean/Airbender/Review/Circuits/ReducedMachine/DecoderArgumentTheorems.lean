import Airbender.Proofs.ReducedMachine.NativeDecoderArguments
import Airbender.Proofs.ReducedMachine.NativeDecoderPadding

namespace Airbender.ReducedMachine.NativeDecoderArguments
open Native NativeMemoryBoundary Airbender.Blake2Worker

theorem decoder_access {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R}
    (accepted : RowAccepted embed ch w aux) :
    argument embed ch 1 w * aux decoderAuxiliaryLayout.access = embed (w importedConstraintsTraceColumns.execute) :=
  NativeDecoderArgumentProofs.row_equation embed ch accepted

theorem same_main_decoder_arguments {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (decoder : Challenges R)
    (config : Native.WorkerConfiguration Setup) {mains : List (NativeMainArguments.Proof R)}
    {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Accepted embed memory ch pc decoder config mains batch inputs inverse) :
    NativeMainArguments.Effects embed memory pc mains batch inputs ∧
    ∀ proof ∈ mains, ∀ i < decoderAuxiliaryLayout.traceLength-1,
      argument embed decoder 1 (proof.memory.rows i) * proof.memory.auxiliary i decoderAuxiliaryLayout.access =
        embed (proof.memory.rows i importedConstraintsTraceColumns.execute) :=
  NativeDecoderArgumentProofs.joint_effects embed memory ch pc decoder config accepted

/-- Local complete-body/decoder-access boundary only; this supplies no global
    accepted proof, attack, defect or inactive caller-filter assumption. -/
theorem inactive_request_local_decoder {R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (ch : Challenges R) :
    ∃ w : Nat → ZMod mersenne31Modulus, ∃ aux : QuarticColumn → R,
      RowAccepted embed ch w aux ∧ w importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest w = ⟨1,1991,some 0,3⟩ :=
  NativeDecoderPaddingProofs.inactive_observations embed ch
end Airbender.ReducedMachine.NativeDecoderArguments
