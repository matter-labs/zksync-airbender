import Airbender.Proofs.ReducedMachine.NativeCallerMixedQueries

namespace Airbender.NativeCallerMixedQueries
open Airbender.NativeCallerRequests (F)
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Every actual dynamic tuple equals its full mixed opcode contribution and
    belongs to the actual runtime pool. No mask, activity or query premise. -/
theorem native_caller_mixed_queries {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table)) : RuntimeRowEffects w :=
  Airbender.NativeCallerMixedQueryProofs.runtime holds

/-- SAME counted source/public image/log20/OLD logical boundaries retain exact
    aggregate key accounting and derive all mixed tuples/memberships on EVERY
    ordinary caller row, including inactive rows. Individual caller Booleanity,
    activity and per-call accounting are still open. No new acceptance boundary. -/
theorem native_counted_caller_mixed_queries {Setup R : Type} [Field R]
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
    Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs ∧
      Airbender.NativeCallerMixedQueries.Effects batch.main.proofs :=
  Airbender.NativeCallerMixedQueryProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeCallerMixedQueries
