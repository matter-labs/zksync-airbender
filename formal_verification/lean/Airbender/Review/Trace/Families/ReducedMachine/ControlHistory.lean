import Airbender.Review.Trace.Families.ReducedMachine.CallerPosition

namespace Airbender.NativeControlHistory
open Airbender.NativeWorkerSnapshot Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
abbrev address : Nat := Nat.pair 0 (Nat.pair 12 0)
def initial : Token := Airbender.NativeMemoryTokens.encodeKey (registerInitialKey 12)
def terminal (inputs : PublicBoundary) : Token := Airbender.NativeMemoryTokens.encodeKey (registerFinalKey inputs 12)
def limbs (token : Token) : Nat × Nat := Nat.unpair token.value
/-- Actual two-limb worker control update; the incoming low limb is retained. -/
def Updated (edge : Token × Token) : Prop :=
  (limbs edge.2).1 = 0 ∧ (limbs edge.2).2 = Airbender.NativeWorkerSchedule.nextHigh (limbs edge.1).2

def MainEdge {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (edge : Token × Token) : Prop :=
  ∃ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, edge ∈ row.memorySteps

/-- Complete x12 raw-token path, including EVERY active MAIN refresh/reset and
    every active worker control port. The path is derived, never supplied. All
    other ports and inactive rows remain in the unchanged source acceptance. -/
structure History {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (inputs : PublicBoundary) (path : List Token) : Prop where
  first : path.head? = some initial
  last : path.getLast? = some (terminal inputs)
  ordered : (path.map Airbender.NativeCompleteMemoryPaths.rank).Pairwise (· < ·)
  distinct : (path.map Airbender.NativeCompleteMemoryPaths.rank).Nodup
  ports : (path.zip path.tail).Perm ((Airbender.NativeMemoryRoots.steps proofs workers).filter fun edge => edge.1.address = address)
  classified : ∀ edge ∈ path.zip path.tail, MainEdge proofs edge ∨
    ∃ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 ∧
      edge = (read w 42,write w 42) ∧ Updated edge
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
    (read w 42,write w 42) ∈ path.zip path.tail

/-- The old request/accounting/joint-execution results remain. This control
    history does not establish caller activity, a one-hot round schedule, standard
    full hash, original Sail worker execution or physical cryptographic refinement. -/
structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeCallerPosition.Effects batch workers inputs
  history : ∃ path, History batch.main.proofs workers inputs path
end Airbender.NativeControlHistory

