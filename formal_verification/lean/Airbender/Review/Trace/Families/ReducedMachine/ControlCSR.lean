import Airbender.Review.Trace.Families.ReducedMachine.ControlOrigin

namespace Airbender.NativeControlCSR
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Actual decoded CSR write semantics. The oracle is an observation, not a
    supplied nondeterminism stream or original CSR execution result. -/
structure CSRResult (w : Nat → F) (entry : CSRProgramEntry) : Prop where
  key : entry.data.immediate.lo = 1984 ∨ entry.data.immediate.lo = 1991
  written : limbs (Airbender.NativeMainDependencies.write w 2) =
    if entry.data.rd = 0 then (0,0) else ((w 90).val,(w 91).val)
  clear : entry.data.immediate.lo = 1991 → limbs (Airbender.NativeMainDependencies.write w 2) = (0,0)

/-- A control origin is ordinary seven-profile code or nondeterminism CSR1984.
    Delegation CSR1991 cannot produce nonzero control high. -/
def SeedSource (entry : Airbender.NativeCallerDecoder.Program) : Prop :=
  (∃ data, unifiedDecoderFields entry.instruction = some data) ∨
  (∃ data, csrDecoderFields entry.instruction = some data ∧ data.immediate.lo = 1984)

def Origin {R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (target : Token) : Prop :=
  ∃ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∃ entry ∈ publicSetup.program,
    entry.SourceWith before Airbender.NativeCallerDecoder.decoderFields ∧ row.decoderQuery = entry.query ∧ entry.data.rd = 12 ∧
    (Airbender.NativeMainDependencies.read row.assignment 2).address = address ∧
    (limbs (Airbender.NativeMainDependencies.read row.assignment 2)).2 = 0 ∧
    (limbs (Airbender.NativeMainDependencies.write row.assignment 2)).2 ≠ 0 ∧
    Airbender.NativeCompleteMemoryPaths.rank (Airbender.NativeMainDependencies.write row.assignment 2) ≤
      Airbender.NativeCompleteMemoryPaths.rank target ∧ SeedSource entry

structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlOrigin.Effects before publicSetup batch workers inputs
  main : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : CSRProgramEntry,
    csrDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → CSRResult row.assignment entry
  origins : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Origin before publicSetup batch.main.proofs token) ∧
    (∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : CSRProgramEntry,
      csrDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → entry.data.rd = 12 →
      (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail)
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
    (w 135).val ≠ 0 → Origin before publicSetup batch.main.proofs (read w 42)
end Airbender.NativeControlCSR

