import Airbender.Proofs.Keccak.SplitNativeMemoryProjection
import Airbender.Proofs.Keccak.SplitPhysicalStep

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Actual native constraints and exact initialized Sail history give the
original complete physical split step in both cache modes. -/
theorem native_physical_step (cached : Bool) (row : Row babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached fixedSetup))
    (active : row.assignment (row.columns cached).execute = 1)
    (index : Fin 361) {before after : State} (arguments : ArgumentsAt index.val before)
    (boundedReads : ∀ port ∈ row.ports cached, (readToken row.assignment port).word.Bounded)
    {cells : List Cell} {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((row.memorySteps cached).map transferEvent))
    (observed : ∀ port ∈ row.ports cached, ∃ cell : Cell,
      cell.addressCode = port.address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment port).word.toBitVec before)
    (pointer : BitVec 32) (pointerRead : (Cell.register 11).read before = .ok pointer before)
    {initial final : Call.Proofs.LaneState}
    (beforeSnapshot : Call.Proofs.PhysicalSnapshot before pointer initial)
    (afterSnapshot : Call.Proofs.PhysicalSnapshot after pointer final) :
    final = Call.Proofs.microStep index initial := by
  obtain ⟨actualPointer, input, kind, actualPointerRead, inputBounds, reads, _, written, frame⟩ :=
    native_call_memory_projection cached row holds active index arguments boundedReads history permutation observed
  have same := (EStateM.Result.ok.inj (actualPointerRead.symm.trans pointerRead)).1
  subst actualPointer
  apply Call.Proofs.physical_step_of_words index pointer input inputBounds beforeSnapshot afterSnapshot
  · intro lane live
    exact reads lane (kind ▸ live)
  · intro lane live high
    exact written lane (kind ▸ live) high
  · intro physical high untouched value read
    exact frame physical high (fun lane live => untouched lane (kind.symm ▸ live)) value read

end Airbender.Keccak.Split.Native.Proofs
