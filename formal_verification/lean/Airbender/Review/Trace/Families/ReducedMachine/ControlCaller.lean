import Airbender.Review.Trace.Families.ReducedMachine.ControlSource

namespace Airbender.NativeControlCaller
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlFold Airbender.NativeControlLastReset Airbender.NativeControlSource
open Airbender.NativeDelegationSupport (callerRows callerKey workerKey)
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Original COMPLETE caller and worker indices, exact activity/request weights
    and FULL four-field key. An inactive MAIN request remains eligible. -/
def CallerAt {Setup R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (workers : WorkerBatch Setup R) (edge : Token × Token) (caller : Fin (callerRows proofs).length) : Prop :=
  ∃ source : Fin (Airbender.NativeTokenLedger.workerRows workers).length, SourceAt workers edge source ∧
    (callerRows proofs)[caller.val] 92 = 1 ∧
    callerKey (callerRows proofs)[caller.val] = workerKey (Airbender.NativeTokenLedger.workerRows workers)[source.val]

def PathMatching {Setup R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (workers : WorkerBatch Setup R) (path : List Token) : Prop :=
  (∀ index : Fin (path.length-1), WorkerEdge workers (pathEdge path index) →
    ∃! caller, CallerAt proofs workers (pathEdge path index) caller) ∧
  (∀ caller : Fin (callerRows proofs).length, (callerRows proofs)[caller.val] 92 = 1 →
    ∃! index : Fin (path.length-1), CallerAt proofs workers (pathEdge path index) caller)

def SegmentCaller {Setup R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (workers : WorkerBatch Setup R) (path : List Token) (target : Fin path.length) (start : Fin (target.val+1))
    (caller : Fin (callerRows proofs).length) : Prop :=
  ∃ index : Fin (target.val-start.val), CallerAt proofs workers
    (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩) caller

/-- Count ORIGINAL caller indices linked to the actual segment, not issued calls. -/
noncomputable def callerCount {Setup R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (workers : WorkerBatch Setup R) (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) : Nat := by
  classical
  exact Fintype.card {caller // SegmentCaller proofs workers path target start caller}

def Accounting {Setup R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (workers : WorkerBatch Setup R) (path : List Token) : Prop :=
  PathMatching proofs workers path ∧ ∀ target : Fin path.length, ∀ start : Fin (target.val+1),
    workerCount workers path target start = callerCount proofs workers path target start

/-- Same path, full prior effects and a DERIVED matching/counts-or-large scope.
    Request-positive inactive callers remain; physical issuance is separate. -/
structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlSource.Effects before publicSetup batch workers inputs
  path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token) ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path ∧
    Edges wordMemoryDecoderFields batch.main.proofs path ∧
    (∀ target : Fin path.length, Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers path target) ∧
    (∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ target : Fin path.length, path.get target = read w 42 ∧ Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers path target) ∧
    Airbender.NativeControlSource.Matching workers path ∧
    (∀ target : Fin path.length, ∀ start : Fin (target.val+1),
      workerCount workers path target start = sourceCount workers path target start) ∧
    (∀ index : Fin (path.length-1), WorkerEdge workers (pathEdge path index) →
      ∃ caller, CallerAt batch.main.proofs workers (pathEdge path index) caller) ∧
    (Accounting batch.main.proofs workers path ∨ 257 ≤ batch.countWord.toNat)
end Airbender.NativeControlCaller
