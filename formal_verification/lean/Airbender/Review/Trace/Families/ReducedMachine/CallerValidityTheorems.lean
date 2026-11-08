import Airbender.Proofs.ReducedMachine.NativeCallerValidity

namespace Airbender.NativeCallerValidity
open Airbender.NativeCallerRequests (F)
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL native BODY derives zero-or-one requests, raw key1991/bounded ABI and
    competing lookup flag isolation, on active AND inactive rows. No valid-mask,
    activity, expected key/value/range or Booleanity premise. This does not derive
    physical activity, original CSR/Sail execution or per-call fulfillment. -/
theorem native_caller_validity {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table)) : RowEffects w :=
  Airbender.NativeCallerValidityProofs.body holds

/-- SAME counted source/public image/log20/OLD logical boundaries retain exact
    aggregate accounting and joint execution, and derive individual validity on
    ALL ordinary caller rows. Activity/per-call accounting remain open. -/
theorem native_counted_caller_validity {Setup R : Type} [Field R]
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
      Airbender.NativeCallerMixedQueries.Effects batch.main.proofs ∧
        Airbender.NativeCallerValidity.Effects batch.main.proofs :=
  Airbender.NativeCallerValidityProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeCallerValidity
