import Airbender.Proofs.ReducedMachine.NativeMixedReplay

namespace Airbender.NativeMixedReplay
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
private abbrev F := ZMod mersenne31Modulus

/-- Same complete source and old explicit formal identity derive a serialization
    of ALL active raw ports from actual seeds to actual teardown. Every read is
    the exact current token. Equal ranks at different addresses are allowed.
    Inactive ports remain in physical source acceptance and its full ledger.
    This is no clock recoding, worker round schedule or original Sail result. -/
theorem native_memory_token_replay {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Execution proofs workers inputs :=
  NativeMixedReplayProofs.effects embed memory ch pc gamma config accepted identity

/-- The same counted public source additionally retains initialized word bounds
    and all prior capacity/dependency results. LogicalLookups and SourceIdentity
    remain explicit cryptographic boundaries, not physical enforcement proofs.
    Original seven-profile Sail still excludes CSR/MOP; public scope excludes MOP. -/
theorem native_counted_mixed_memory_replay {Setup R : Type} [Field R]
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
  NativeMixedReplayProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeMixedReplay
