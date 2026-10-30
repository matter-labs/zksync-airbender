import Airbender.Proofs.Keccak.SplitNativeCallExecution
import Airbender.Proofs.Keccak.SplitCallMemoryProjection

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- The actual native call has the exact original touched-word values and
retains every untouched physical word. The public control fixes its index. -/
theorem native_call_memory_projection (cached : Bool) (row : Row babyBearModulus)
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
        cell.read before = .ok (readToken row.assignment port).word.toBitVec before) :
    ∃ (pointer : BitVec 32) (input : Vector Nat 7),
      kindAt index.val = row.kind ∧
      (Cell.register 11).read before = .ok pointer before ∧
      (∀ lane : Fin 7, input[lane] < 2 ^ 64) ∧
      (∀ lane : Fin 7, lane.val < Call.slotCount row.kind →
        (Call.laneCell pointer (Call.slots index)[lane] false).read before = .ok (Call.half input[lane] false) before ∧
        (Call.laneCell pointer (Call.slots index)[lane] true).read before = .ok (Call.half input[lane] true) before) ∧
      (∀ lane : Fin 7, (Call.result index input)[lane] < 2 ^ 64) ∧
      (∀ (lane : Fin 7), lane.val < Call.slotCount row.kind → ∀ high : Bool,
        (Call.laneCell pointer (Call.slots index)[lane] high).read after =
          .ok (Call.half (Call.result index input)[lane] high) after) ∧
      (∀ (physical : Fin 31) (high : Bool),
        (∀ lane : Fin 7, lane.val < Call.slotCount row.kind → (Call.slots index)[lane] ≠ physical) →
        ∀ value : BitVec 32,
          (Call.laneCell pointer physical high).read before = .ok value before →
          (Call.laneCell pointer physical high).read after = .ok value after) := by
  obtain ⟨actual, pointer, input, kind, actualArguments, pointerRead, reads, writes⟩ :=
    native_call_executes cached row holds active index arguments boundedReads history permutation observed
  have same := Call.Proofs.arguments_index_injective arguments actualArguments
  subst actual
  obtain ⟨_, expectedPointer, _, expectedRead, _, _, aligned⟩ := arguments
  have pointerEqual := (EStateM.Result.ok.inj (expectedRead.symm.trans pointerRead)).1
  rw [pointerEqual] at aligned
  let canonical : Vector Nat 7 := Vector.ofFn fun lane : Fin 7 =>
    if live : lane.val < Call.slotCount row.kind then input[lane] else 0
  have agree (lane : Fin 7) (live : lane.val < Call.slotCount (kindAt index.val)) : input[lane] = canonical[lane] := by
    have supported : lane.val < Call.slotCount row.kind := kind ▸ live
    simp [canonical, supported]
  have inputBounds (lane : Fin 7) : canonical[lane] < 2 ^ 64 := by
    simp only [canonical, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · rename_i live
      exact (reads lane live).1
    · decide
  have outputs := Call.Proofs.result_live_congr index input canonical agree
  have execution : AtomicWrites (Call.writes index pointer (Call.result index canonical)) before after := by
    rw [← Call.Proofs.writes_live_congr index pointer _ _ outputs]
    exact writes
  refine ⟨pointer, canonical, kind, pointerRead, inputBounds, ?_,
    Call.Proofs.result_lane_bound index canonical inputBounds, ?_, ?_⟩
  · intro lane live
    have equal := agree lane (kind.symm ▸ live)
    rw [← equal]
    exact (reads lane live).2
  · intro lane live high
    exact Call.Proofs.written_lane_reads index pointer aligned _ execution lane (kind.symm ▸ live) high
  · intro physical high untouched value read
    apply Call.Proofs.unwritten_lane_frame index pointer aligned _ execution physical high _ value read
    intro lane live
    exact untouched lane (kind ▸ live)

end Airbender.Keccak.Split.Native.Proofs
