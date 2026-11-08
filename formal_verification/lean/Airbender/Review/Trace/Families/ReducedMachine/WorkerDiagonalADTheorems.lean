import Airbender.Proofs.ReducedMachine.NativeWorkerDiagonalAD

namespace Airbender.NativeWorkerDiagonalAD
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL unchanged BODY/actual fixed pool derives all second diagonal A carries,
    sum/D-input bounds and four exact D XOR/rotate8 results. -/
theorem native_worker_diagonal_ad {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerDiagonalADProofs.mixing holds

/-- SAME counted source, original public image/log20 and OLD explicit logical
    boundaries derive second diagonal A wrapping additions and chained D rotate8
    from derived inputs and canonical ten-weight selected messages. Every ordinary
    worker, including inactive, retains all prior initialized replay/bound/capacity/
    control effects, column G, routing and first-half diagonal G. Zero/multiple
    masks remain. No expected read/range/result, one-hot mask, round, schedule or
    history premise. All ports and caller requests stay. Public scope excludes MOP;
    original seven-profile Sail excludes CSR/MOP. Second C/B, full worker hash,
    finalization/native writes and physical schedules/accounting remain open. -/
theorem native_counted_worker_diagonal_ad {Setup R : Type} [Field R]
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
  NativeWorkerDiagonalADProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerDiagonalAD
