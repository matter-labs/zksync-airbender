import Airbender.Review.Trace.Families.ReducedMachine.ControlLoad

namespace Airbender.NativeControlLastReset
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Consecutive original path positions strictly before the chosen target.
    Both getters are bounded; no out-of-domain token or clock recoding. -/
def edgeAt {A : Type} (path : List A) (target : Fin path.length) (index : Fin target.val) : A × A :=
  (path[index.val]'(Nat.lt_trans index.isLt target.isLt),
   path[index.val+1]'(Nat.lt_of_le_of_lt (Nat.succ_le_of_lt index.isLt) target.isLt))

/-- Relevant means an actual MAIN value change. Copies, including equal-value
    third-port writes, still remain as full raw-token edges in the path. -/
def Relevant {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (edge : Token × Token) : Prop :=
  MainEdge proofs edge ∧ edge.1.value ≠ edge.2.value

def PublicWrite {R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (edge : Token × Token) : Prop :=
  ∃ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∃ entry ∈ publicSetup.program,
    entry.SourceWith before Airbender.NativeCallerDecoder.decoderFields ∧ row.decoderQuery = entry.query ∧ entry.data.rd = 12 ∧
    edge = (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∧ edge.1.address = address ∧
    ((limbs edge.2).2 ≠ 0 → Airbender.NativeControlCSR.SeedSource entry)

/-- Every retained suffix position is an actual value-copy MAIN edge or actual
    active worker42 update. Equal-value worker updates remain worker occurrences. -/
def WorkerOrCopy {Setup R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (workers : WorkerBatch Setup R) (edge : Token × Token) : Prop :=
  (MainEdge proofs edge ∧ edge.1.value = edge.2.value) ∨
    ∃ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 ∧
      edge = (read w 42,write w 42) ∧ Updated edge

def Suffix {Setup R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (workers : WorkerBatch Setup R) (path : List Token) (target : Fin path.length) (start : Nat) : Prop :=
  ∀ index : Fin target.val, start ≤ index.val → ¬ Relevant proofs (edgeAt path target index) ∧
    WorkerOrCopy proofs workers (edgeAt path target index)

/-- Either no MAIN value change occurs from the seed to this target, or one
    original fetched rd12 third-port write is the LAST such change. The complete
    following segment retains every MAIN copy and worker edge, with exact tokens. -/
def Outcome {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) : Prop :=
  ((limbs (path.get target)) = (0,0) ∧ Suffix proofs workers path target 0) ∨
    ∃ index : Fin target.val, Relevant proofs (edgeAt path target index) ∧
      PublicWrite before publicSetup proofs (edgeAt path target index) ∧
      ((limbs (path.get target)).2 ≠ 0 → (limbs (edgeAt path target index).2).2 ≠ 0) ∧
      Suffix proofs workers path target (index.val+1)

structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlLoad.Effects before publicSetup batch workers inputs
  path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token) ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path ∧
    Edges wordMemoryDecoderFields batch.main.proofs path ∧
    (∀ target : Fin path.length, Outcome before publicSetup batch.main.proofs workers path target) ∧
    (∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ target : Fin path.length, path.get target = read w 42 ∧ Outcome before publicSetup batch.main.proofs workers path target)
end Airbender.NativeControlLastReset
