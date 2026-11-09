import Airbender.Review.Trace.Families.ReducedMachine.ControlHistory

namespace Airbender.NativeControlOrigin
open Airbender.NativeControlHistory Airbender.NativeWorkerSnapshot
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- An ACTUAL executing MAIN third-port write to GPR12, bound to an original
    fetched public entry with rd12, which changes the high field from zero to
    nonzero no later than the target. Both complete raw tokens are retained. -/
def Origin {R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (target : Token) : Prop :=
  ∃ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∃ entry ∈ publicSetup.program,
    entry.SourceWith before Airbender.NativeCallerDecoder.decoderFields ∧ row.decoderQuery = entry.query ∧ entry.data.rd = 12 ∧
    (Airbender.NativeMainDependencies.read row.assignment 2).address = address ∧
    (limbs (Airbender.NativeMainDependencies.read row.assignment 2)).2 = 0 ∧
    (limbs (Airbender.NativeMainDependencies.write row.assignment 2)).2 ≠ 0 ∧
    Airbender.NativeCompleteMemoryPaths.rank (Airbender.NativeMainDependencies.write row.assignment 2) ≤
      Airbender.NativeCompleteMemoryPaths.rank target

/-- Nonzero controls have a derived actual public MAIN-write origin. No desired
    reset, activity, round, one-hot mask or schedule is added to acceptance. -/
structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlHistory.Effects batch workers inputs
  origins : ∃ path, Airbender.NativeControlHistory.History batch.main.proofs workers inputs path ∧
    ∀ token ∈ path, (limbs token).2 ≠ 0 → Origin before publicSetup batch.main.proofs token
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
    (w 135).val ≠ 0 → Origin before publicSetup batch.main.proofs (read w 42)
end Airbender.NativeControlOrigin

