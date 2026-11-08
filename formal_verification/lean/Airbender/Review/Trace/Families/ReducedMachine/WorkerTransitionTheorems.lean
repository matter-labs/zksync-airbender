import Airbender.Proofs.ReducedMachine.NativeWorkerTransition

namespace Airbender.NativeWorkerTransition
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- SAME counted source and original public image/log20 derive EVERY ordinary
    worker's complete pure transition from actual reads, including inactive rows.
    Actual ports1..24 and42 equal eight state results, sixteen extended results
    and the x12 update. Both control reads and all ten weighted round bits remain;
    no witness intermediate/output, desired result, one-hot mask or schedule is
    supplied. Prior eight G results, all43 ports, raw times and initialized exact
    replay/word bounds remain. OLD logical boundaries are explicit. This is one
    weighted-mask transition, not a physical round sequence or scheduled full hash.
    Public scope excludes MOP; original seven-profile Sail excludes CSR/MOP.
    Inactive caller activity, converse accounting, physical cryptography,
    completeness and parity remain open. -/
theorem native_counted_worker_transition {Setup R : Type} [Field R]
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
  NativeWorkerTransitionProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeWorkerTransition
