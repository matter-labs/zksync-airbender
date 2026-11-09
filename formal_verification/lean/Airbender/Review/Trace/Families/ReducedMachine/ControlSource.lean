import Airbender.Review.Trace.Families.ReducedMachine.ControlFold

namespace Airbender.NativeControlSource
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlFold Airbender.NativeControlLastReset
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- All consecutive original path positions; both actual token getters are bounded. -/
def pathEdge {A : Type} (path : List A) (index : Fin (path.length-1)) : A × A :=
  (path[index.val]'(by have := index.isLt; omega),path[index.val+1]'(by have := index.isLt; omega))

/-- Original COMPLETE workerRows index, including inactive positions in its domain.
    The relation selects activity and exact full control read/write tokens. -/
def SourceAt {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) (edge : Token × Token)
    (source : Fin (Airbender.NativeTokenLedger.workerRows workers).length) : Prop :=
  let w := (Airbender.NativeTokenLedger.workerRows workers)[source.val]
  w constraintsABI.multiplicity = 1 ∧ edge = (read w 42,write w 42)

/-- Both directions identify UNIQUE original positions, not deduplicated rows. -/
def Matching {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) (path : List Token) : Prop :=
  (∀ index : Fin (path.length-1), WorkerEdge workers (pathEdge path index) →
    ∃! source, SourceAt workers (pathEdge path index) source) ∧
  (∀ source : Fin (Airbender.NativeTokenLedger.workerRows workers).length,
    (Airbender.NativeTokenLedger.workerRows workers)[source.val] constraintsABI.multiplicity = 1 →
    ∃! index : Fin (path.length-1), SourceAt workers (pathEdge path index) source)

def SegmentSource {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) (path : List Token)
    (target : Fin path.length) (start : Fin (target.val+1))
    (source : Fin (Airbender.NativeTokenLedger.workerRows workers).length) : Prop :=
  ∃ index : Fin (target.val-start.val), SourceAt workers
    (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩) source

/-- Cardinality of ORIGINAL worker-source indices whose exact edge lies in the
    segment. No expected count or schedule is supplied. -/
noncomputable def sourceCount {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) (path : List Token)
    (target : Fin path.length) (start : Fin (target.val+1)) : Nat := by
  classical
  exact Fintype.card {source // SegmentSource workers path target start source}

/-- Original source positions and exact counts on the SAME complete fold path.
    Issued calls, physical scheduling and standard hash remain separate. -/
structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlFold.Effects before publicSetup batch workers inputs
  path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token) ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path ∧
    Edges wordMemoryDecoderFields batch.main.proofs path ∧
    (∀ target : Fin path.length, Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers path target) ∧
    (∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ target : Fin path.length, path.get target = read w 42 ∧ Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers path target) ∧
    Matching workers path ∧
    (∀ target : Fin path.length, ∀ start : Fin (target.val+1),
      workerCount workers path target start = sourceCount workers path target start)
end Airbender.NativeControlSource
