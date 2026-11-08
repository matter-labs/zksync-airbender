import Airbender.Proofs.ReducedMachine.NativeWorkerDiagonalG

namespace Airbender.NativeWorkerDiagonalG
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL unchanged native BODY/actual fixed pool derives second diagonal C
    carries/sum bounds and all four exact B XOR/rotate7 results. -/
theorem native_worker_diagonal_final_cb {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerDiagonalGProofs.mixing holds

/-- SAME counted source, original public image/log20 and OLD explicit logical
    boundaries derive second C additions/B rotations and ALLFOUR complete diagonal
    G results on derived routed column outputs/canonical ten-weight messages.
    Every prior column G, initialized replay/bound/capacity/control effect stays,
    including inactive ordinary workers. No expected read/range/result, one-hot
    mask, round, schedule or history premise. All ports and caller requests stay.
    Public scope excludes MOP; original seven-profile Sail excludes CSR/MOP.
    These intermediate G outputs are not yet final native writes or a scheduled
    standard worker hash. Finalization/physical schedules/accounting remain open. -/
theorem native_counted_worker_diagonal_g {Setup R : Type} [Field R]
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
  NativeWorkerDiagonalGProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerDiagonalG
