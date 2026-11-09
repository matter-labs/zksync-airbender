import Airbender.Review.Trace.Families.ReducedMachine.ControlLastReset

namespace Airbender.NativeControlFold
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLastReset Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Count every selected original position, including equal-value updates. -/
def countFlags : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n+1, flags => countFlags (fun index => flags index.castSucc) + if flags (Fin.last n) then 1 else 0

def advance (value : Nat × Nat) : Nat × Nat := (0,Airbender.NativeWorkerSchedule.nextHigh value.2)
def iterate {A : Type} (step : A → A) : Nat → A → A
  | 0, value => value
  | n+1, value => step (iterate step n value)

/-- Exact active worker42 raw edge membership; no value-change filter. This
    observable does not identify original worker-source occurrence positions. -/
def WorkerEdge {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) (edge : Token × Token) : Prop :=
  ∃ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 ∧ edge = (read w 42,write w 42)

noncomputable def workerFlags {Setup R : Type} [Field R] (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) : Fin (target.val-start.val) → Bool := by
  classical
  exact fun index => decide (WorkerEdge workers (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩))

noncomputable def workerCount {Setup R : Type} [Field R] (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) : Nat := countFlags (workerFlags workers path target start)

def Fold {Setup R : Type} [Field R] (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) : Prop :=
  limbs (path.get target) = iterate advance (workerCount workers path target start)
    (limbs (path.get ⟨start.val,by have := start.isLt; have := target.isLt; omega⟩))

def Outcome {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) : Prop :=
  (limbs (path.get target) = (0,0) ∧ Suffix proofs workers path target 0 ∧ Fold workers path target 0) ∨
    ∃ index : Fin target.val, Relevant proofs (edgeAt path target index) ∧
      PublicWrite before publicSetup proofs (edgeAt path target index) ∧
      ((limbs (path.get target)).2 ≠ 0 → (limbs (edgeAt path target index).2).2 ≠ 0) ∧
      Suffix proofs workers path target (index.val+1) ∧ Fold workers path target ⟨index.val+1,by have := index.isLt; omega⟩

structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlLastReset.Effects before publicSetup batch workers inputs
  path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token) ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path ∧
    Edges wordMemoryDecoderFields batch.main.proofs path ∧
    (∀ target : Fin path.length, Outcome before publicSetup batch.main.proofs workers path target) ∧
    (∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ target : Fin path.length, path.get target = read w 42 ∧ Outcome before publicSetup batch.main.proofs workers path target)
end Airbender.NativeControlFold
