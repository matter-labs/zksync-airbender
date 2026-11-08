import Airbender.Proofs.ReducedMachine.NativeWorkerSnapshot

namespace Airbender.NativeWorkerSnapshot
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- SAME counted source and original public image/log20 derive a common exact
    initialized pre-state for every actual active worker's ALL43 ports. The cut
    precedes every write at its noninjective proof rank. Read tokens are present
    and unique at their addresses; snapshot samples decode to the actual reference
    inputs, and all25writable outputs equal the complete weighted transition.
    Distinct addresses, common BOTH-field write time and strict old-read progress
    are derived. Full prior replay/word bounds/ordinary inactive transitions stay.
    No desired snapshot, read, value, range, result, schedule or one-hot premise.
    OLD logical boundaries remain explicit. Grouped post-state/frame, physical
    round sequencing, scheduled hash, CSR/MOP/worker Sail, converse accounting,
    physical cryptography, completeness and parity remain open. -/
theorem native_counted_worker_snapshot {Setup R : Type} [Field R]
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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Effects batch workers inputs :=
  NativeWorkerSnapshotProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerSnapshot
