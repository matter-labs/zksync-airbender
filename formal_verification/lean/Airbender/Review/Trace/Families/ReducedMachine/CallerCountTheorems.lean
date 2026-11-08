import Airbender.Proofs.ReducedMachine.NativeCallerCount

namespace Airbender.NativeCallerCount
open Airbender.NativeDelegationSupport Airbender.Trace Airbender.ReducedMachine.Native
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- The SAME counted source derives exact natural per-key counts modulo the
    characteristic and at most31 characteristic multiples. The quotient is NOT
    assumed zero. All original inactive caller occurrences remain. Activity,
    per-call matching and physical cryptographic extraction remain open. -/
theorem native_counted_caller_counts {Setup R : Type} [Field R]
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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeCallerCount.Effects batch workers inputs :=
  Airbender.NativeCallerCountProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeCallerCount
