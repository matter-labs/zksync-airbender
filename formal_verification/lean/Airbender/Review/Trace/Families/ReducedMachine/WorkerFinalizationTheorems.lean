import Airbender.Proofs.ReducedMachine.NativeWorkerFinalization

namespace Airbender.NativeWorkerFinalization
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL unchanged BODY/actual fixed pool derives the actual control selector and
    ALL8 state words: XOR configured/read base with actual two extended outputs
    when selected, otherwise preserve the actual previous state-read word. -/
theorem native_worker_finalization {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerFinalizationProofs.finalization holds

/-- SAME counted source, original image/log20 and OLD explicit logical boundaries
    retain all8 G results, actual16 extended writes and initialized exact raw-token
    replay; EVERY ordinary worker gains all8 final state-write results, including
    inactive rows. No expected read/range/result, one-hot mask, round, schedule or
    history premise. Zero/multiple masks, all43 ports and caller requests stay.
    Public scope excludes MOP; original seven-profile Sail excludes CSR/MOP.
    Standard scheduled full hash/physical round schedules, inactive caller activity,
    converse accounting and physical cryptography/completeness/parity stay open. -/
theorem native_counted_worker_finalization {Setup R : Type} [Field R]
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
  NativeWorkerFinalizationProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerFinalization
