import Airbender.Proofs.ReducedMachine.NativeWorkerSecondCB

namespace Airbender.NativeWorkerSecondCB
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL native BODY/actual fixed pool derives second C carries, C bounds and
    B XOR/rotate7 for all four column calls. -/
theorem native_worker_second_cb {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerSecondCBProofs.mixing holds

/-- SAME counted source, original public image/log20 and OLD explicit logical
    boundaries derive second C wrapping additions and B XOR/rotate7, and assemble
    actual outputs of ALLFOUR COLUMN calls into pure G on derived pre-G inputs
    and weighted messages. Every ordinary worker, including inactive, retains all
    prior exact replay/bounds/capacity/dependencies/control/arithmetic effects.
    No expected read/range/result, one-hot mask, round, schedule or history premise.
    All ports and caller requests stay. Public scope excludes MOP; original seven-
    profile Sail excludes CSR/MOP. Diagonal calls, finalization/full hash, physical
    schedules/accounting remain open. Arbitrary masks do not imply standard rounds. -/
theorem native_counted_worker_column_g {Setup R : Type} [Field R]
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
  NativeWorkerSecondCBProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerSecondCB
