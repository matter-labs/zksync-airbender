import Airbender.Proofs.ReducedMachine.NativeWorkerDiagonalCB

namespace Airbender.NativeWorkerDiagonalCB
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL unchanged native BODY/actual fixed pool derives all four first diagonal
    C carries/sum bounds and B XOR/rotate12 results, including native re-chunking. -/
theorem native_worker_diagonal_cb {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerDiagonalCBProofs.mixing holds

/-- SAME counted source, original public image/log20 and OLD explicit logical
    boundaries derive all four first diagonal C wrapping additions/B rotations
    and assemble first-half G on derived routed column outputs/weighted messages.
    Every previous initialized replay/bound/capacity/control/column G effect stays,
    including inactive ordinary workers. No expected read/range/result, one-hot
    mask, round, schedule or history premise. All ports and caller requests stay.
    Public scope excludes MOP; original seven-profile Sail excludes CSR/MOP.
    Second diagonal A/D-C/B, finalization/full hash, physical schedules/accounting
    remain open. Arbitrary masks do not imply a standard scheduled round. -/
theorem native_counted_worker_diagonal_cb {Setup R : Type} [Field R]
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
  NativeWorkerDiagonalCBProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerDiagonalCB
