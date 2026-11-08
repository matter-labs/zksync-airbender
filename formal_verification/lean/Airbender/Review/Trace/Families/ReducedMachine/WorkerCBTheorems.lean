import Airbender.Proofs.ReducedMachine.NativeWorkerCB

namespace Airbender.NativeWorkerCB
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL native BODY/actual fixed pool derives first C/B carries, both input/
    result limb bounds and exact XOR/rotate12 in all four column calls. Natural
    C wrapping additions additionally follow from initialized inputs below. -/
theorem native_worker_first_cb {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerCBProofs.mixing holds

/-- SAME counted source, original public image/log20 and OLD explicit logical
    boundaries derive initialized C wrapping additions and B XOR/rotate12 for
    EVERY ordinary worker, including inactive rows. Prior exact raw-token replay,
    capacity, dependencies, initialization, weighted messages and A/D effects stay.
    No expected read, range, result, round, one-hot mask, schedule or history premise.
    All ports/caller requests stay. Public scope excludes MOP; original seven-profile
    Sail excludes CSR/MOP. Remaining G/hash, physical schedule/accounting stay open. -/
theorem native_counted_worker_first_cb {Setup R : Type} [Field R]
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
  NativeWorkerCBProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerCB
