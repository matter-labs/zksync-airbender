import Airbender.Proofs.ReducedMachine.NativeWorkerSchedule

namespace Airbender.NativeWorkerSchedule
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL352-equation/296-query BODY derives actual control bits, compression
    inputs, all32 selected-message limbs and x12 update. No expected one-hot mask,
    round, read value, schedule or hash output is supplied. -/
theorem native_worker_message_schedule {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) : RowEffects w :=
  NativeWorkerScheduleProofs.row holds

/-- SAME counted public source and old explicit logical boundaries retain the
    complete initialized raw-token replay/word bounds and derive pointwise effects
    for EVERY ordinary worker, including inactive rows. No caller filter is added.
    Original seven-profile Sail still excludes CSR/MOP; public scope excludes MOP.
    Standard hash-round results and physical/converse accounting remain open. -/
theorem native_counted_worker_message_schedule {Setup R : Type} [Field R]
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
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, RowEffects w :=
  NativeWorkerScheduleProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerSchedule
