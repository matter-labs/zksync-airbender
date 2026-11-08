import Airbender.Proofs.ReducedMachine.NativeWorkerAddition

namespace Airbender.NativeWorkerAddition
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- SAME complete counted public source and old explicit logical boundaries
    derive initialized pre-G/compression inputs, canonical ten-weight messages and
    first wrapping additions in all four column G calls. Old exact XOR/rotate16,
    full raw-token replay, capacity and dependencies remain. No expected read,
    range, result, one-hot mask, round, schedule or history is supplied. Every
    ordinary worker, including inactive rows, is covered; caller requests stay.
    Public scope excludes MOP; original seven-profile Sail excludes CSR/MOP.
    Remaining G/hash, physical schedule and converse accounting remain open. -/
theorem native_counted_worker_first_addition {Setup R : Type} [Field R]
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
  NativeWorkerAdditionProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerAddition
