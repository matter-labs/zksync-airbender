import Airbender.Proofs.ReducedMachine.NativeWorkerExtendedOutput

namespace Airbender.NativeWorkerExtendedOutput
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- FULL unchanged BODY binds all32 actual extended-state write limbs to the
    checked diagonal results, with the native A/B/C/D destination permutation. -/
theorem native_worker_extended_writes {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    ∀ diagonal component : Fin 4, ∀ limb : Fin 2,
      writeLimb w (destination diagonal component) limb = resultLimb w diagonal component limb :=
  NativeWorkerExtendedOutputProofs.limbs holds

/-- Actual output chunk bounds identify all16 packed memory-write words. -/
theorem native_worker_extended_output {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    ∀ word : Fin 16, writeWord w word =
      (Airbender.NativeWorkerDiagonalG.diagonalResult w (diagonalOf word))[componentOf word] :=
  NativeWorkerExtendedOutputProofs.written holds

/-- SAME counted source/original public image/log20/OLD logical boundaries derive
    all16 actual extended writes as pure G results on DERIVED routed inputs and
    weighted messages, retaining all prior column/diagonal arithmetic and exact
    initialized raw-token replay, including inactive ordinary workers. No expected
    read/result, one-hot mask, round, schedule or history premise. All43 ports and
    caller requests stay. Public scope excludes MOP; original Sail excludes CSR/MOP.
    First8-state finalization, full worker reference hash, physical round schedules,
    caller activity/converse accounting and physical cryptography remain open. -/
theorem native_counted_worker_extended_output {Setup R : Type} [Field R]
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
  NativeWorkerExtendedOutputProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerExtendedOutput
