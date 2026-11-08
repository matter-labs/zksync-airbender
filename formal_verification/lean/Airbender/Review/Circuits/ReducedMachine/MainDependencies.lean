import Airbender.Review.Circuits.ReducedMachine.WorkerWriteWords
import Airbender.Review.Circuits.ReducedMachine.WordMemory

namespace Airbender.NativeMainDependencies
open Airbender.ReducedMachine.Native
abbrev F := ZMod mersenne31Modulus
abbrev MainRow := Airbender.NativeMixedMemoryOrder.MainRow

def port (slot : Fin 3) : Trace.MemoryPort := importedConstraintsMemoryPorts[slot]
def readWord (w : Nat → F) (slot : Fin 3) : Vector F 2 := (port slot).readValue.evaluate w
def writeWord (w : Nat → F) (slot : Fin 3) : Vector F 2 :=
  ((port slot).writeValue.getD (port slot).readValue).evaluate w
def read (w : Nat → F) (slot : Fin 3) := Trace.readToken w (port slot)
def write (w : Nat → F) (slot : Fin 3) := Trace.writeToken importedConstraintsTraceColumns w (port slot)

/-- Exact value copies only. Raw refresh times, the store OLDREAD and unmasked
    store write remain. The observed native SW packed mask is conclusion scope;
    no instruction profile or per-row mask is supplied to full BODY acceptance. -/
structure LocalEffects (w : Nat → F) : Prop where
  readonly : ∀ slot : Fin 3, slot.val < 2 → writeWord w slot = readWord w slot
  store : w 12 = (wordMemoryMask true : F) → writeWord w 2 = readWord w 1

/-- Derived dependencies for actual execute1 main rows, including CSR/MOP memory
    observations. This establishes no CSR/MOP Sail effect or initialized bound. -/
structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : Airbender.Blake2Worker.Native.WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  workers : Airbender.NativeWorkerWriteWords.Effects proofs batch inputs
  localRows : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, LocalEffects row.assignment
  writes : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∀ slot,
    Airbender.NativeCompleteMemoryPaths.rank (write row.assignment slot) = row.clock+slot.val
  sources : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∀ slot,
    read row.assignment slot ∈ Airbender.NativeLatestReads.available proofs batch
  before : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∀ source target : Fin 3,
    source.val ≤ target.val → Airbender.NativeCompleteMemoryPaths.rank (read row.assignment source) <
      Airbender.NativeCompleteMemoryPaths.rank (write row.assignment target)
end Airbender.NativeMainDependencies
