import Airbender.Proofs.ReducedMachine.NativeWorkerGroup

namespace Airbender.NativeWorkerGroup
open Airbender.NativeWorkerSnapshot Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- SAME counted source/original public image/log20 and OLD logical boundaries
    derive a contiguous ALL43-port worker block in the SAME complete raw-token
    replay, exact post-state writes, unaffected-address frame and continuation to
    the actual terminal state. Snapshot samples decode actual reference inputs;
    post-state samples decode ALL25weighted-reference outputs. ALL18readonly
    refreshes remain. Other equal-rank edge occurrences stay in the residual;
    distinct addresses/common raw write times/strict progress are derived.
    No desired state, read, result, one-hot mask, schedule or history premise.
    MAIN partial dependencies stay. Rank is noninjective proof order only.
    Physical round sequence/standard scheduled hash, inactive caller activity,
    converse accounting, CSR/MOP/worker Sail, physical cryptography, completeness
    and parity remain open. -/
theorem native_counted_worker_group {Setup R : Type} [Field R]
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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeWorkerGroup.Effects batch workers inputs :=
  NativeWorkerGroupProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerGroup
