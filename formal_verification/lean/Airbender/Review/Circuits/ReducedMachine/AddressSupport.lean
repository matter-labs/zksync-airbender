import Airbender.Review.Circuits.ReducedMachine.MemoryRoots

namespace Airbender.NativeAddressSupport
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
abbrev Token := Trace.MemoryToken mersenne31Modulus

/-- Canonical raw native address, before compression or STAGE2 truncation.
    RAM includes the observed ROM-shadow region; alignment, permissions and
    independent public-domain coverage are separately scoped. -/
def Domain (address : MemoryKeyAddress) : Prop :=
  (address.isRegister = 1 ∧ address.low.val < 32 ∧ address.high = 0) ∨
    (address.isRegister = 0 ∧ address.low.val < 65536 ∧ address.high.val < 65536)

/-- Canonical field address of an actual typed seed cell. No current read value
    or worker result is specified by this address projection. -/
def cellAddress : Trace.Cell → MemoryKeyAddress
  | .register index => ⟨1,index.toNat,0⟩
  | .ram address =>
    let word := Arithmetic.Word.ofBitVec address
    ⟨0,word.lo,word.hi⟩

/-- Same-source seed address support and raw address domains for active ports.
    This does not assert initialized value bounds, online history, STAGE2 key
    identity, RAM-only worker pointers or original CSR/MOP/worker Sail effects. -/
structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  roots : Airbender.NativeMemoryRoots.Effects proofs batch inputs
  cells : ∀ read write, Airbender.NativeMixedMemoryOrder.Step proofs batch read write →
    ∃ cell ∈ Airbender.NativeInitializationSeedBoundary.cells proofs,
      read.address = cell.addressCode ∧ write.address = cell.addressCode
  mains : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∀ port ∈ row.ports,
    Domain (Airbender.ReducedMachine.NativeMainAuxiliary.nativeAddress row.assignment port.address)
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, w constraintsABI.multiplicity = 1 →
    ∀ slot : Fin 43, Domain (quotientMemoryKey w slot false).address
end Airbender.NativeAddressSupport
