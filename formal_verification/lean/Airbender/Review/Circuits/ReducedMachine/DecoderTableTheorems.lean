import Airbender.Proofs.ReducedMachine.NativeDecoderTableArguments

namespace Airbender.ReducedMachine.NativeDecoderTableArguments
open Native NativeDecoderArguments NativeMemoryBoundary Airbender.Blake2Worker

theorem decoder_table_auxiliary_sum {R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (ch : Challenges R)
    {proof : Proof R} (accepted : TableAccepted embed ch proof) :
    auxiliarySum proof true = auxiliarySum proof false :=
  NativeDecoderTableArgumentProofs.auxiliary_sum embed ch accepted

theorem same_main_decoder_table_arguments {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (decoder : Challenges R)
    (config : Native.WorkerConfiguration Setup) {proofs : List (Proof R)}
    {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Accepted embed memory ch pc decoder config proofs batch inputs inverse) :
    NativeMainArguments.Effects embed memory pc (proofs.map Proof.main) batch inputs ∧
      ∀ proof ∈ proofs, auxiliarySum proof true = auxiliarySum proof false :=
  NativeDecoderTableArgumentProofs.joint_effects embed memory ch pc decoder config accepted
end Airbender.ReducedMachine.NativeDecoderTableArguments
