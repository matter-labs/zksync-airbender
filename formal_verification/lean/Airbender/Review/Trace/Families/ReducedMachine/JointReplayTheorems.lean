import Airbender.Proofs.ReducedMachine.NativeJointReplay

namespace Airbender.NativeJointReplay
open Airbender.NativeWorkerSnapshot Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- SAME counted source/public image/log20/OLD logical boundaries derive ONE
    initialized grouped execution for every actual active worker and every MAIN
    port singleton. Flattened permutation retains every original edge occurrence.
    Each worker's common reads, exact post-state, frame and all25weighted-reference
    outputs occur within THIS shared execution. Tied proof ranks are permitted;
    MAIN partial dependencies and all43worker ports/raw timestamps remain.
    No desired reads, results, masks, schedule or history premise. This proof
    order is not physical round sequencing or a standard scheduled full hash.
    Caller activity/converse accounting, original CSR/MOP/worker Sail, physical
    cryptography, completeness and parity remain open. -/
theorem native_counted_joint_replay {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeJointReplay.Effects batch workers inputs :=
  NativeJointReplayProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeJointReplay
