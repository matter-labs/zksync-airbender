import Airbender.Review.Circuits.ReducedMachine.WorkerSignedClocks

namespace Airbender.NativeMixedMemoryOrder
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
abbrev Token := Trace.MemoryToken mersenne31Modulus
abbrev MainRow := Trace.Row mersenne31Modulus Trace.NativeReducedFamily

def mainRows {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) :=
  Airbender.NativeMainStateHistory.rows (Airbender.NativeInitializationBatch.mainProofs proofs)

/-- Actual active main or worker memory step. All raw token fields remain.
    This is an observed edge, not a supplied expected read/source/history.
    Inactive worker accesses stay in full acceptance and its read ledger;
    this relation makes no strict-order claim for their zero-clock loops. -/
def Step {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (read write : Token) : Prop :=
  (∃ row ∈ mainRows proofs, ∃ port ∈ row.ports,
    read = Trace.readToken row.assignment port ∧ write = Trace.writeToken row.columns row.assignment port) ∨
  (∃ w ∈ Airbender.NativeTokenLedger.workerRows batch, w constraintsABI.multiplicity = 1 ∧
    ∃ slot : Fin 43, read = Airbender.NativeWorkerClockProgress.readToken w slot ∧
      write = Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true))

def NoCycles {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) : Prop :=
  ∀ token, ¬ Relation.TransGen (Step proofs batch) token token

/-- Derived order on every actual main port and every mixed active step.
    The signed measure is not injective and never replaces raw timestamps.
    No initialized history, seed path or compiler/physical enforcement is claimed. -/
structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) : Prop where
  workers : Airbender.NativeWorkerSignedClocks.Effects proofs batch
  mains : ∀ row ∈ mainRows proofs, ∀ port ∈ row.ports,
    Airbender.NativeWorkerSignedClocks.value (Trace.readToken row.assignment port).time <
      Airbender.NativeWorkerSignedClocks.value (Trace.writeToken row.columns row.assignment port).time
  steps : ∀ read write, Step proofs batch read write →
    Airbender.NativeWorkerSignedClocks.value read.time < Airbender.NativeWorkerSignedClocks.value write.time
  cycles : NoCycles proofs batch
end Airbender.NativeMixedMemoryOrder
