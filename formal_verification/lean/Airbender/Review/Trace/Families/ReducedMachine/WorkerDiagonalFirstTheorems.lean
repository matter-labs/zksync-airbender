import Airbender.Proofs.ReducedMachine.NativeWorkerDiagonalFirst

namespace Airbender.NativeWorkerDiagonalFirst
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL unchanged native BODY/actual fixed pool derives all four first diagonal
    A carry/sum bounds and exact D XOR/rotate16 results. -/
theorem native_worker_diagonal_first {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerDiagonalFirstProofs.mixing holds

/-- SAME counted source, original public image/log20 and OLD explicit logical
    boundaries derive canonical routed post-column inputs and four first diagonal
    wrapping additions/D rotations, retaining every previous column G and exact
    initialized raw-token replay/bound/capacity/control effect, including inactive
    ordinary workers. Weighted messages and zero/multiple round masks remain.
    No expected read/range/result, one-hot mask, round, schedule or history premise.
    All ports and caller requests stay. Public scope excludes MOP; original seven-
    profile Sail excludes CSR/MOP. Remaining diagonal steps/finalization/full hash,
    physical schedules/accounting stay open. -/
theorem native_counted_worker_diagonal_first {Setup R : Type} [Field R]
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
  NativeWorkerDiagonalFirstProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerDiagonalFirst
