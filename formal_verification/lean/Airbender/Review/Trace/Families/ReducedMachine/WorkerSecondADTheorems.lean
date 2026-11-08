import Airbender.Proofs.ReducedMachine.NativeWorkerSecondAD

namespace Airbender.NativeWorkerSecondAD
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL native BODY/actual fixed pool derives second A carry bits, A/D limb
    bounds and exact XOR/rotate8 in all four column calls. -/
theorem native_worker_second_ad {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerSecondADProofs.mixing holds

/-- SAME counted source, original public image/log20 and OLD explicit logical
    boundaries derive second A wrapping additions and D XOR/rotate8 chained to
    the actual first D results. All ordinary worker rows, including inactive,
    retain prior exact raw-token replay, bounds, capacity, dependencies, weighted
    messages and first A/D/C/B effects. No expected read/range/result, one-hot mask,
    round, schedule or history premise. All ports and caller requests stay.
    Public scope excludes MOP; original seven-profile Sail excludes CSR/MOP.
    Second C/B, diagonal calls, full hash, physical schedules/accounting stay open. -/
theorem native_counted_worker_second_ad {Setup R : Type} [Field R]
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
  NativeWorkerSecondADProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerSecondAD
